module Project

%default total
%access public export

record GenModule where
  constructor GenMod
  fileName : String
  moduleName : String
  genExpr : List String

||| Example:
|||   templates
|||     Free.fs
|||   source
|||     Queries.fspp
|||   generate
|||     EnvQry.fs
|||       module MyNamespace.EnvQry
|||       gen EnvQry
|||       gen Free EnvQry
|||     FSQry.fs
|||       module MyNamespace.FSQry
|||       gen FSQry
|||       gen Free FSQry
record Project where
  constructor Proj
  templates, source : List String
  generate : List GenModule

Semigroup Project where
  p <+> q =
    let t = templates p <+> templates q
        s = source p <+> source q
        g = generate p <+> generate q
    in Proj t s g

Monoid Project where
  neutral = Proj [] [] []

ofTmpl : List String -> Project
ofTmpl t = Proj t [] []

ofSrc : List String -> Project
ofSrc s = Proj [] s []

ofGen : List GenModule -> Project
ofGen g = Proj [] [] g

Token : Type
Token = (Nat, String)

data Error
  = OddNSpaces Nat
  | UnrecognizedTopLevel String
  | UnexpectedIndentation Nat String

tokenizeOne : List Char -> Either Error (Maybe Token)
tokenizeOne = tokenize1 Z where
  tokenize1 : Nat -> List Char -> Either Error (Maybe Token)
  tokenize1 _ [] = Right Nothing
  tokenize1 _ (_ :: []) = Right Nothing
  tokenize1 k (' ' :: ' ' :: cs) = tokenize1 (S k) cs
  tokenize1 k (' ' :: _ :: _) = Left (OddNSpaces (k * 2 + 1))
  tokenize1 k cs@(_ :: _ :: _) = Right $ Just (k, pack cs)

tokenize : String -> Either (List (Nat, Error)) (List Token)
tokenize text =
  let ls = lines text
      lineNs = take (length ls) $ iterate S Z
      results = zip lineNs $ map (tokenizeOne . unpack) ls
  in foldr addResult (Right []) results where
    addResult : (Nat, Either Error (Maybe Token))
              -> Either (List (Nat, Error)) (List Token)
              -> Either (List (Nat, Error)) (List Token)
    addResult (k, Left e) (Left l) = Left ((k, e) :: l)
    addResult (_, _) x@(Left _) = x
    addResult (_, Right Nothing) x@(Right _) = x
    addResult (_, Right (Just tok)) (Right toks) = Right (tok :: toks)
    addResult (k, Left e) (Right _) = Left [(k, e)]

dropPlus1Smaller : (x : a) -> (xs : List a) -> (n : Nat)
                 -> Smaller (List.drop n xs) (x :: xs)
dropPlus1Smaller x [] Z = LTESucc LTEZero
dropPlus1Smaller x [] (S k) = LTESucc LTEZero
dropPlus1Smaller x (y :: xs) Z = lteRefl
dropPlus1Smaller x (y :: ys) (S k) =
  LTESucc $ lteSuccLeft $ dropPlus1Smaller x ys k

parseGenMods : List Token -> Either Error (List GenModule)
parseGenMods toks = ?blargh

step : (xs : List Token)
     -> ((ys : List Token) -> Smaller ys xs -> Project -> Either Error Project)
     -> Project -> Either Error Project
step [] _ p = Right p
step (x@(Z, "templates") :: xs) f p =
  let tmpls = map snd $ takeWhile ((== 1) . fst) xs
      p' = p <+> ofTmpl tmpls
      n = length tmpls
      rem = drop n xs in
  f rem (dropPlus1Smaller x xs n) p
step (x@(Z, "source") :: xs) f p =
  let srcs = map snd $ takeWhile ((== 1) . fst) xs
      p' = p <+> ofSrc srcs
      n = length srcs
      rem = drop n xs in
  f rem (dropPlus1Smaller x xs n) p
step (x@(Z, "generate") :: xs) f p =
  let raw = takeWhile ((> 0) . fst) xs in
  case parseGenMods raw of
    Left e => Left e
    Right genMods =>
      let p' = p <+> ofGen genMods
          n = length raw
          rem = drop n xs in
      f rem (dropPlus1Smaller x xs n) p
step ((Z,  x) :: _) _ _ = Left $ UnrecognizedTopLevel x
step ((S n,  x) :: _) _ _ = Left $ UnexpectedIndentation (S n) x

parseToks : List Token -> Either Error Project
parseToks toks =
  let addToProject = sizeRec step toks
  in addToProject neutral

parse : String -> Project
parse x = ?parse_rhs

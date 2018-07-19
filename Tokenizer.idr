module Tokenizer

%default total
%access public export

record MacroHeader where
  constructor MacroH
  indent : Nat
  name : String
  params : List String

space : Nat -> Char -> Maybe Nat
space x y =
  if isSpace y
  then Just (x + 1)
  else Nothing

startsWith : List Char -> List Char -> Maybe (List Char)
startsWith [] [] = Just []
startsWith [] (x :: xs) = Just (x :: xs)
startsWith (y :: xs) [] = Nothing
startsWith (y :: xs) (x :: ys) =
  if y == x
  then startsWith xs ys
  else Nothing

parseHeaderWith : String -> Nat -> List Char -> Maybe MacroHeader
parseHeaderWith kw x ('/' :: '/' :: '#' :: cs) =
  startsWith (unpack kw) cs
  >>= \cs' =>
    case words $ pack cs' of
    [] => Nothing
    name :: params => Just $ MacroH x name params
parseHeaderWith _ _ _ = Nothing

parseHeaderTok' : String -> Nat -> List Char -> Maybe MacroHeader
parseHeaderTok' _ x [] = Nothing
parseHeaderTok' kw x (c :: cs) =
  case space x c of
    Nothing => parseHeaderWith kw x (c :: cs)
    Just x => parseHeaderTok' kw x cs

parseHeaderTok : String -> String -> Maybe MacroHeader
parseHeaderTok kw = parseHeaderTok' kw 0 . unpack

parseFooter : String -> String -> Bool
parseFooter x = (==) ("//#end" ++ x) . trim

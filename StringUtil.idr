||| Why do we have to do this?
||| https://stackoverflow.com/q/51529100/834176
module StringUtil

%default total
%access public export

data Break = Brk
data Chunk a
  = OpenCh (List a)
  | Sealed (List a)

chunkCtr : Maybe Break -> List a -> Chunk a
chunkCtr Nothing    = OpenCh
chunkCtr (Just Brk) = Sealed

extractChunk : Chunk a -> List a
extractChunk (OpenCh l) = l
extractChunk (Sealed l) = l

mutual
  break : List a -> Maybe Break
  break [] = Just Brk
  break (_ :: _) = Nothing

  fullOrFill : Eq a => (m : List a) -> {auto prf : NonEmpty m}
                    -> List a -> (l : List a ** NonEmpty l)
  fullOrFill m {prf} [] = (m ** prf)
  fullOrFill _ (x :: xs) = (x :: xs ** IsNonEmpty)

  specialCons : (List a -> Chunk a) -> a -> List (Chunk a) -> List (Chunk a)
  specialCons ctr x [] = [ctr [x]]
  specialCons ctr x ((OpenCh y) :: ys) = ctr (x :: y) :: ys
  specialCons _ x tail@((Sealed _) :: _) = OpenCh [x] :: tail

  split' : Eq a => (delim : List a)    -> {auto dprf : NonEmpty delim   }
                -> (matching : List a) -> {auto mprf : NonEmpty matching}
                -> Maybe Break -> List a -> List (Chunk a)
  split' _ _ _ [] = []
  split' delim m@(_::m') maybeBreak list@(x::xs) =
    if isPrefixOf m list
    then
      let brk = break m' in
      let (newM ** _) = fullOrFill delim m' in
      split' delim newM brk xs
    else specialCons (chunkCtr maybeBreak) x $ split' delim delim Nothing xs

split : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
             -> List a -> List (List a)
split delim = map extractChunk . split' delim delim Nothing

||| One wonders if this is horribly inefficient... it is odd that since Idris
||| uses primitive strings it does not have basic primitive string functions like
||| replace
partial
strReplace : String -> String -> String -> String
strReplace needle replacement =
  case unpack needle of
    [] => id
    (n :: ns) => pack . intercalate (unpack replacement) . split (n :: ns) . unpack

lenEq : (l : List a) -> (m : List b) -> Maybe (length l = length m)
lenEq [] [] = Just Refl
lenEq (x :: xs) (y :: ys) = map cong $ lenEq xs ys
lenEq _ _ = Nothing

tests : List (List (List Char))
tests =
  [ split [' ', 'b']      $ unpack "foo bar baz qux"
  , split [' ']           $ unpack "foo bar baz qux"
  , split ['x']           $ unpack "foo bar baz qux"
  , split ['u']           $ unpack "foo bar baz qux"
  , split ['r', ' ', 'b'] $ unpack "foo bar baz qux"
  ]

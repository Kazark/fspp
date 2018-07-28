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
  onMatch : Eq a => (delim : List a)    -> {auto dprf : NonEmpty delim   }
                 -> (matching : List a) -> {auto mprf : NonEmpty matching}
                 -> (l : List a) -> {auto lprf : NonEmpty l}
                 -> List (Chunk a)
  onMatch delim (_::m') list@(x::xs) =
    case m' of
      []       => split' delim delim (Just Brk) xs
      (m_::ms) => split' delim (m_ :: ms) Nothing xs

  specialCons : Maybe Break -> a -> List (Chunk a) -> List (Chunk a)
  specialCons _ x [] = [OpenCh [x]]
  specialCons maybeBreak x ((OpenCh y) :: ys) = (chunkCtr maybeBreak (x :: y)) :: ys
  specialCons _ x tail@((Sealed _) :: _) = (OpenCh [x]) :: tail

  noMatch : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
                 -> Maybe Break
                 -> (l : List a) -> {auto lprf : NonEmpty l}
                 -> List (Chunk a)
  noMatch delim maybeBreak (x::xs) =
    specialCons maybeBreak x $ split' delim delim Nothing xs

  split' : Eq a => (delim : List a)    -> {auto dprf : NonEmpty delim   }
                -> (matching : List a) -> {auto mprf : NonEmpty matching}
                -> Maybe Break -> List a -> List (Chunk a)
  split' _ _ _ [] = []
  split' delim m maybeBreak list@(_::_) =
    if isPrefixOf m list
    then onMatch delim m list
    else noMatch delim maybeBreak list

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

test : List (List Char)
test = split [' ', 'b'] $ unpack "foo bar baz qux"

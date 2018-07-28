||| Why do we have to do this?
||| https://stackoverflow.com/q/51529100/834176
module StringUtil

%default total
%access public export

data Break = Brk

break : List a -> Maybe Break
break [] = Just Brk
break (_ :: _) = Nothing

fullOrFill : Eq a => (m : List a) -> {auto prf : NonEmpty m}
                  -> List a -> (l : List a ** NonEmpty l)
fullOrFill m {prf} [] = (m ** prf)
fullOrFill _ (x :: xs) = (x :: xs ** IsNonEmpty)

onBreak : Break -> (List a, List (List a)) -> (List a, List (List a))
onBreak Brk (l, ls) = ([], l :: ls)

split' : Eq a => (delim : List a)    -> {auto dprf : NonEmpty delim   }
              -> (matching : List a) -> {auto mprf : NonEmpty matching}
              -> Maybe Break -> List a -> (List a, List (List a))
split' _ _ _ [] = ([], [])
split' delim m@(_::m') maybeBreak list@(x::xs) =
  if isPrefixOf m list
  then
    let brk = break m' in
    let (newM ** _) = fullOrFill delim m' in
    split' delim newM brk xs
  else
    let (l, ls) = split' delim delim Nothing xs in
    foldr onBreak (x :: l, ls) maybeBreak

split : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
             -> List a -> List (List a)
split delim [] = []
split delim list@(_::_) = uncurry (::) $ split' delim delim Nothing list

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

testData : List (String, String, String)
testData =
  [ (" b", "_a", "foo bar baz qux")
  , (" ", "-", "foo bar baz qux")
  , ("x", "y", "foo bar baz qux")
  , ("u", "vv", "foo bar baz qux")
  , ("r b", "x", "foo bar baz qux")
  , ("foo", "oof", "foo bar baz qux")
  , ("oo", "||", "foo bar baz qux")
  , ("r b", "bah", "")
  , ("", "", "bah")
  ]

test : List String
test = map (\(x, y, z) => strReplace x y z) testData

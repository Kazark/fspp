||| Why do we have to do this?
||| https://stackoverflow.com/q/51529100/834176
module StringUtil

%default total
%access public export

fullOrFill : Eq a => (m : List a) -> {auto prf : NonEmpty m}
                  -> List a -> (l : List a ** NonEmpty l)
fullOrFill m {prf} [] = (m ** prf)
fullOrFill _ (x :: xs) = (x :: xs ** IsNonEmpty)

splitOnL' : Eq a => (delim : List a)    -> {auto dprf : NonEmpty delim   }
              -> (matching : List a) -> {auto mprf : NonEmpty matching}
              -> List a -> (List a, List (List a))
splitOnL' _ _ [] = ([], [])
splitOnL' delim m@(_::m') list@(x::xs) =
  if isPrefixOf m list
  then
    let (newM ** _) = fullOrFill delim m' in
    let (l, ls) = splitOnL' delim newM xs in
    case m' of
      [] => ([], l :: ls)
      (_ :: _) => (l, ls)
  else
    let (l, ls) = splitOnL' delim delim xs in
    (x :: l, ls)

splitOnL : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
             -> List a -> List (List a)
splitOnL delim [] = []
splitOnL delim list@(_::_) = uncurry (::) $ splitOnL' delim delim list

||| One wonders if this is horribly inefficient... it is odd that since Idris
||| uses primitive strings it does not have basic primitive string functions like
||| replace
partial
strReplace : String -> String -> String -> String
strReplace needle replacement =
  case unpack needle of
    [] => id
    (n :: ns) => pack . intercalate (unpack replacement) . splitOnL (n :: ns) . unpack

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

testSplit : List (List (List Char))
testSplit =
  map (
    \(x, _, z) =>
      case unpack x of
       [] => []
       (x' :: xs) => splitOnL (x' :: xs) (unpack z)
  ) testData

testReplace : List String
testReplace = map (\(x, y, z) => strReplace x y z) testData

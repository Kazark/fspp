||| Why do we have to do this?
||| https://stackoverflow.com/q/51529100/834176
module ListExt

%default total
%access public export

splitOnL' : Eq a => (delim : List a)    -> {auto dprf : NonEmpty delim   }
              -> (matching : List a) -> {auto mprf : NonEmpty matching}
              -> List a -> (List a, List (List a))
splitOnL' _ _ [] = ([], [])
splitOnL' delim m@(_::m') list@(x::xs) =
  if isPrefixOf m list
  then
    case m' of
      [] => ([], uncurry (::) $ splitOnL' delim delim xs)
      (m_ :: ms) => splitOnL' delim (m_ :: ms) xs
  else
    let (l, ls) = splitOnL' delim delim xs in
    (x :: l, ls)

splitOnL : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
             -> List a -> List (List a)
splitOnL delim [] = []
splitOnL delim list@(_::_) = uncurry (::) $ splitOnL' delim delim list

substitute : Eq a => List a -> List a -> List a -> List a
substitute [] replacement = id
substitute (n :: ns) replacement = intercalate replacement . splitOnL (n :: ns)

strReplace : String -> String -> String -> String
strReplace needle replacement = pack . substitute (unpack needle) (unpack replacement) . unpack

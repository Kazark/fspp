||| Why do we have to do this?
||| https://stackoverflow.com/q/51529100/834176
module ListExt

%default total

mutual
  private
  dropSublist : Eq a => (delim : List a) -> {auto prf : NonEmpty delim}
                     -> List a -> List a -> (List a, List (List a))
  dropSublist _ _ [] = ([], [])
  dropSublist delim [] xs = ([], uncurry (::) $ splitOnSublist' delim xs)
  dropSublist delim (_ :: ys) (_ :: xs) = dropSublist delim ys xs

  private
  splitOnSublist' : Eq a => (delim : List a) -> {auto prf : NonEmpty delim}
                         -> List a -> (List a, List (List a))
  splitOnSublist' _ [] = ([], [])
  splitOnSublist' delim list@(x::xs) =
    if isPrefixOf delim list
    then dropSublist delim delim list
    else
      let (l, ls) = splitOnSublist' delim xs in
      (x :: l, ls)

splitOnSublist : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
             -> List a -> List (List a)
splitOnSublist delim [] = []
splitOnSublist delim list@(_::_) = uncurry (::) $ splitOnSublist' delim list

substitute : Eq a => List a -> List a -> List a -> List a
substitute [] replacement = id
substitute (n :: ns) replacement = intercalate replacement . splitOnSublist (n :: ns)

strReplace : String -> String -> String -> String
strReplace needle replacement = pack . substitute (unpack needle) (unpack replacement) . unpack

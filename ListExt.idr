||| Why do we have to do this?
||| https://stackoverflow.com/q/51529100/834176
module ListExt

%default total
%access public export

splitOnSublist' : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
                       -> (state : Maybe (List a))
                       -> List a -> (List a, List (List a))
splitOnSublist' _ _ [] = ([], [])
splitOnSublist' delim (Just []) xs =
  ([], uncurry (::) $ splitOnSublist' delim Nothing xs)
splitOnSublist' delim (Just (_ :: ms)) (_::xs) =
  splitOnSublist' delim (Just ms) xs
splitOnSublist' delim Nothing list@(x::xs) =
  if isPrefixOf delim list
  then splitOnSublist' delim (Just delim) list
  else
    let (l, ls) = splitOnSublist' delim Nothing xs
    in (x :: l, ls)

splitOnSublist : Eq a => (delim : List a) -> {auto dprf : NonEmpty delim}
             -> List a -> List (List a)
splitOnSublist delim [] = []
splitOnSublist delim list@(_::_) = uncurry (::) $ splitOnSublist' delim Nothing list

substitute : Eq a => List a -> List a -> List a -> List a
substitute [] replacement = id
substitute (n :: ns) replacement = intercalate replacement . splitOnSublist (n :: ns)

strReplace : String -> String -> String -> String
strReplace needle replacement = pack . substitute (unpack needle) (unpack replacement) . unpack

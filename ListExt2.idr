module ListExt2

%default total
%access public export

smallerThanCons : (x : a) -> (xs : List a) -> Smaller xs (x :: xs)
smallerThanCons x [] = lteRefl
smallerThanCons x (y :: xs) = lteRefl

||| If Left True, never bother to call me back
eat : Eq a => (delim : List a) -> {auto prf : NonEmpty delim}
    -> (dish : List a)
    -> Either Bool (rem : List a ** Smaller rem dish)
eat (x :: xs) [] = Left True
eat (x :: xs) (y :: ys) =
  if x == y
  then
    case xs of
      [] => Right (ys ** smallerThanCons y ys)
      (z :: zs) =>
        case eat (z :: zs) ys of
          Left e => Left e
          Right (l ** prf) => Right (l ** lteSuccRight prf)
  else Left False

splitStep : Eq a => (xs : List a)
          -> ((ys : List a) -> Smaller ys xs -> List a
                            -> (List a, List (List a)))
          -> List a -> (List a, List (List a))
splitStep [] _ _ = ([], [])
splitStep xs@(_ :: _) _ [] = (xs, [])
splitStep (x :: xs) f delim@(_::_) =
  case eat delim (x :: xs) of
    Left True => (x :: xs, [])
    Left False =>
      let (l, ls) = f xs (smallerThanCons x xs) delim
      in (x :: l, ls)
    Right (rem ** prf) =>
      let (l, ls) = f rem prf delim
      in ([], l::ls)

splitWith : Eq a => List a -> List a -> List (List a)
splitWith delim splittee =
  let splitter = sizeRec splitStep splittee
  in uncurry (::) $ splitter delim

substitute : Eq a => List a -> List a -> List a -> List a
substitute needle replacement = intercalate replacement . splitWith needle

strReplace : String -> String -> String -> String
strReplace needle replacement =
  pack . substitute (unpack needle) (unpack replacement) . unpack

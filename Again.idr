module Again

%default total
%access public export

||| A "full" or non-empty list
FList : Type -> Type
FList a = (xs : List a ** NonEmpty xs)

infixr 5 :::

(:::) : a -> List a -> FList a
(:::) x xs = ((x :: xs) ** IsNonEmpty)

||| Proof that the first list is an improper prefix of the second list, with the
||| third list as the remainder.
data IsPrefixOf : FList a -> FList a -> List a -> Type where
  SingletonPrefix : IsPrefixOf (x ::: []) (x ::: rem) rem
  SuccPrefix : IsPrefixOf (xs ** _) (ys ** _) rem
             -> IsPrefixOf (x ::: xs) (x ::: ys) rem


prefixAntisym : (xs : FList a) -> (ys : FList a) -> (zs : List a)
              -> IsPrefixOf xs ys zs -> IsPrefixOf ys xs zs
              -> (xs = ys, zs = [])
prefixAntisym (xs ** xpf) (ys ** ypf) [] SingletonPrefix _ impossible
prefixAntisym (xs ** xpf) (ys ** ypf) [] (SuccPrefix _) _ impossible
prefixAntisym (xs ** xpf) (ys ** ypf) (_ :: _) SingletonPrefix _ impossible
prefixAntisym (xs ** xpf) (ys ** ypf) (_ :: _) (SuccPrefix _) _ impossible

prefixAntisym' : (xs : FList a) -> (ys : FList a) -> (zs : List a)
               -> IsPrefixOf xs ys zs -> IsPrefixOf ys xs zs
               -> (xs = ys, zs = [])
prefixAntisym' ((x :: []) ** IsNonEmpty) ((x :: []) ** IsNonEmpty) [] SingletonPrefix SingletonPrefix = (Refl, Refl)
prefixAntisym' ((x :: []) ** IsNonEmpty) ((y :: (y' :: ys)) ** IsNonEmpty) [] ipo1 ipo2 = ?prefixAntisym'_rhs_5
prefixAntisym' ((x :: (x' :: xs)) ** IsNonEmpty) ((y :: []) ** IsNonEmpty) [] ipo1 ipo2 = ?prefixAntisym'_rhs_1
prefixAntisym' ((x :: (x' :: xs)) ** IsNonEmpty) ((y :: (y' :: ys)) ** IsNonEmpty) [] ipo1 ipo2 = ?prefixAntisym'_rhs_6
prefixAntisym' ((x :: xs) ** IsNonEmpty) ((y :: ys) ** IsNonEmpty) (z :: zs) ipo1 ipo2 = ?prefixAntisym'_rhs_3

module ListExt3

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

interface PartialOrder (a : Type) (r : a -> a -> Type) where
  reflexive : (x : a) -> r x x
  antisymmetrical : (x : a) -> (y : a) -> r x y -> r y x -> x = y
  transitive : (x : a) -> (y : a) -> (z : a) -> r x y -> r y z -> r x z

prefixRefl : (xs : FList a) -> IsPrefixOf xs xs []
prefixRefl ((x :: []) ** IsNonEmpty) = SingletonPrefix
prefixRefl ((x :: (y :: xs)) ** IsNonEmpty) =
  -- TODO do whatever is needed to make Idris happy rather than assert_total
  SuccPrefix $ assert_total $ prefixRefl (y ::: xs)

prefixAntisym : (xs : FList a) -> (ys : FList a) -> (zs : List a)
              -> IsPrefixOf xs ys zs -> IsPrefixOf ys xs zs
              -> (xs = ys, zs = [])
prefixAntisym (xs ** xpf) (ys ** ypf) [] SingletonPrefix _ impossible
prefixAntisym (xs ** xpf) (ys ** ypf) [] (SuccPrefix _) _ impossible
prefixAntisym (xs ** xpf) (ys ** ypf) (_ :: _) SingletonPrefix _ impossible
prefixAntisym (xs ** xpf) (ys ** ypf) (_ :: _) (SuccPrefix _) _ impossible

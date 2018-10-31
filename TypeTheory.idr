||| Simple GADTs for F#
module TypeTheory

%default total
%access public export

||| A term in the language
||| universe 0 - values
||| universe 1 - types
||| universe 2 - kinds
||| universe 2 - sorts
data Term : (universe : Nat) -> Type where
  ||| A named term or variable
  Var : String -> Term u
  ||| An explicit type annotation
  Ann : Term u -> Term (S u) -> Term u
  ||| Function application
  Appl : Term u -> Term u -> Term u
  ||| Type constructor operator. Its terms cannot be values.
  Arrow : Term (S u) -> Term (S u) -> Term (S u)
  ||| The name of Type in any universe starting with 2 (since the lowest Type
  ||| has as its type Kind).
  Tau : Term (S (S n))

||| A primitive type or type constructor in universe one, opaque to the
||| source language because taken for granted as existing in the target
||| language. Syntax:
|||   primitive string : Type
|||   primitive Maybe : Type -> Type
|||   primitive Either : Type -> Type -> Type
||| The term in universe two is the type of the primitive: all primitives
||| have a type of Type or of some type constructor, which are kinds, so it
||| is in universe two.
primType : String -> Term 2 -> Term 1
primType name type = Ann (Var name) type

||| With full dependent types, equality is a problem that needs gamma, and
||| requires evaluation. We do not yet need this.
equal : Term u -> Term u -> Bool
equal (Var a) (Var c) = a == c
equal (Ann a b) (Ann c d) = equal a c && equal b d
equal (Appl a b) (Appl c d) = equal a c && equal b d
equal (Arrow a b) (Arrow c d) = equal a c && equal b d
equal Tau Tau = True
equal _ _ = False

equal' : Term u -> Term v -> Bool
equal' {u} {v} x y =
  case decEq u v of
    Yes prf => equal x (rewrite prf in y)
    No _ => False

||| Typing environment, where its universe is one larger than the universe of
||| the biggest terms for which it contains typing information: or said another
||| way, perhaps more lucidly, the universe off the typing environment is equal
||| to the universe of the types of the biggest terms it contains.
data Gamma : (universe : Nat) -> Type where
  ||| To ensure that the typing information is always cumulative from its
  ||| biggest universe all the way down to values, we must ground the empty
  ||| universe as size zero. This also makes sense with the definition of its
  ||| universe being one larger than the universe of its biggest terms: there is
  ||| no universe below Z and therefore if Z is one larger than the biggest
  ||| terms in Nil there are no terms in Nil.
  Nil : Gamma Z
    -- List (u : Nat ** List (Term u, Term (S u)))
  (::) : List (Term u, Term (S u)) -> Gamma u -> Gamma (S u)

typeInEnv : Gamma v -> Term u -> Maybe (Term (S u))
-- The empty type environment contains no judgements, by definition.
typeInEnv {v=Z} {u=_} [] _ = Nothing
-- u is at least as big as v if not bigger in this case. That means the typing
-- environment is insufficiently large to contain information on this term.
typeInEnv {v=S Z} {u = (S _)} (_ :: _) _ = Nothing
typeInEnv {v=S j} {u = k} (x :: xs) t =
  case decEq k j of
    Yes prf => lookupBy equal t (rewrite prf in x)
    No _ => typeInEnv xs t

checkTypeInEnv : Gamma v -> Term u -> Term (S u) -> Bool
checkTypeInEnv gamma x t =
  let maybeT = typeInEnv gamma x
  in case maybeT of
    Just t' => equal t t'
    Nothing => False

mutual
  check : Gamma v -> Term u -> Term (S u) -> Bool
  check gamma x@(Var _) t = checkTypeInEnv gamma x t
  check _ (Ann _ t) t' = equal t t'
  check gamma (Appl f a) t =
    case synthesize gamma f of
      Just (Arrow at bt) => check gamma a at && equal t bt
      -- The first term in an application must be a function, i.e. must have an
      -- arrow type, else it is bogus and we can't synthesize a type for that
      _ => False
  check _ (Arrow _ _) Tau = True
  check _ (Arrow _ _) _ = False
  check _ Tau Tau = True
  check _ Tau _ = False

  synthesize : Gamma v -> Term u -> Maybe (Term (S u))
  synthesize gamma x@(Var _) = typeInEnv gamma x
  synthesize _ (Ann _ t) = Just t
  synthesize gamma (Appl f a) =
    case synthesize gamma f of
      Just (Arrow at bt) => if check gamma a at then Just bt else Nothing
      -- The first term in an application must be a function, i.e. must have an
      -- arrow type, else it is bogus and we can't synthesize a type for that
      _ => Nothing
  synthesize _ (Arrow _ _) = Just Tau
  synthesize _ Tau = Just Tau

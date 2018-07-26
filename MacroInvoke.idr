module MacroInvoke

import Data.Vect
import Tokenizer
import MacroDef

%default total
%access public export

arity : MacroDef -> Nat
arity = length . params

ArgVect : MacroDef -> Type
ArgVect def = Vect (arity def) String

record MacroInv (def : MacroDef) where
  constructor Invoke
  indent : Nat
  args : ArgVect def

spanList : (List a -> Bool) -> List a -> (List a, List a)
spanList _ [] = ([],[])
spanList func list@(x::xs) =
  if func list
  then
    let (ys,zs) = spanList func xs
    in (x::ys,zs)
  else ([],list)

breakList : (List a -> Bool) -> List a -> (List a, List a)
breakList func = spanList (not . func)

-- Hats off to https://hackage.haskell.org/package/MissingH-1.2.0.0/docs/src/Data-List-Utils.html#replace
partial
split : Eq a => List a -> List a -> List (List a)
split _ [] = []
split delim str =
  let (firstline, remainder) = breakList (isPrefixOf delim) str in
  firstline :: case remainder of
                    [] => []
                    x => if x == delim
                         then [] :: []
                         else split delim (drop (length delim) x)

-- One wonders if this is horribly inefficient... it is odd that since Idris
-- uses primitive strings it does not have basic primitive string functions like
-- replace
partial
strReplace : String -> String -> String -> String
strReplace needle replacement =
  pack . intercalate (unpack replacement) . split (unpack needle) . unpack

lenEq : (l : List a) -> (m : List b) -> Maybe (length l = length m)
lenEq [] [] = Just Refl
lenEq (x :: xs) (y :: ys) = map cong $ lenEq xs ys
lenEq _ _ = Nothing

replace : {l : List b} -> (m : List a) -> (eqPrf : length l = length m) -> Vect (length l) a
replace m eqPrf = rewrite eqPrf in fromList m

applyArgs : (def : MacroDef) -> List String -> Maybe (ArgVect def)
applyArgs (Define _ params _) args = replace args <$> lenEq params args

macroInv : (def : MacroDef) -> MacroHeader -> Maybe (MacroInv def)
macroInv def (MacroH indent _ args) =
  Invoke indent <$> applyArgs def args

data State
  = Outside
  | RunningMacro (MacroInv def)

doingIt : List MacroDef -> State -> List String -> List String
doingIt defs Outside [] = []
doingIt defs Outside (x :: xs) =
  case parseHeaderTok "invoke" x of
    Just h =>
      case find (\d => name h == name d) defs of
        Nothing => doingIt defs Outside xs
        Just d  => ?asdf
    Nothing => doingIt defs Outside xs
doingIt defs (RunningMacro x) [] = []
doingIt defs (RunningMacro y) (x :: xs) =
  if parseFooter "inv" x
  then ?asdf
  else doingIt defs (RunningMacro y) xs

invokeMacros : List MacroDef -> List String -> List String
invokeMacros def = doingIt def Outside

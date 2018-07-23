module MacroInvoke

import Data.Vect
import Tokenizer
import MacroDef

%default total
%access public export

arity : MacroDef -> Nat
arity = length . params

record MacroInv (def : MacroDef) where
  constructor Invoke
  indent : Nat
  args : Vect (arity def) String

strReplace : String -> String -> String -> String
strReplace x y z = ?strReplace_rhs

macroInv : (def : MacroDef) -> MacroHeader -> Maybe (MacroInv def)
macroInv def (MacroH indent _ args) with (arity def == length args) | False = Nothing
macroInv def (MacroH indent _ args) with (arity def == length args) | True  = Just $ Invoke indent $ replace Refl $ fromList args

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

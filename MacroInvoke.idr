module MacroInvoke

import Data.Vect
import Tokenizer
import MacroDef

%default total
%access public export

record MacroInv where
  constructor Invoke
  indent : Nat
  appliedArgs : List (String, String)
  macroBody : List String

{-

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

 -}

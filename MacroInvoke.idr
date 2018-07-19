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
  params : Vect (arity def) String

data State
  = Outside
  | RunningMacro (MacroInv def)

doingIt : State -> List String -> List String
doingIt Outside [] = []
doingIt Outside (x :: xs) =
  case parseHeaderTok "invoke" x of
    Just x => ?asdf
    Nothing => ?asdfasdf
doingIt (RunningMacro x) [] = []
doingIt (RunningMacro y) (x :: xs) =
  if parseFooter "inv" x
  then ?asdf
  else doingIt (RunningMacro y) xs

invokeMacros : List String -> List String
invokeMacros = doingIt Outside

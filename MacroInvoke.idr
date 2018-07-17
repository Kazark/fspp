module MacroInvoke

import Data.Vect
import Tokenizer
import MacroDef

%default total
%access public export

arity : MacroDef -> Nat
arity = length . args

record MacroInv (def : MacroDef) where
  constructor Invoke
  params : Vect (arity def) String

data State
  = Outside
  | RunningMacro (MacroInv def)

doingIt : State -> List String -> List String
doingIt x xs = ?doingIt_rhs

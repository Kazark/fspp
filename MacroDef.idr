module MacroDef

import Tokenizer

%default total
%access public export

record MacroDef where
  constructor Define
  name : String
  args : List String
  body : List String

data ParseOneState
  = NeedBegin
  | NeedEnd MacroHeader (List String)

ParseState : Type
ParseState = (ParseOneState, List MacroDef)

parseMacroDefs' : ParseState -> List String -> List MacroDef
parseMacroDefs' (NeedBegin, macros) [] = macros
parseMacroDefs' (NeedBegin, macros) (x :: xs) =
  case parseHeaderTok "define" x of
    Nothing => parseMacroDefs' (NeedBegin, macros) xs
    Just hd => parseMacroDefs' (NeedEnd hd [], macros) xs
parseMacroDefs' (NeedEnd _ _, macros) [] = macros
parseMacroDefs' (NeedEnd header body, macros) (x :: xs) =
  case parseFooter x of
    False => parseMacroDefs' (NeedEnd header (x :: body), macros) xs
    True  => parseMacroDefs' (NeedBegin, Define (name header) (args header) body :: macros) xs

parseMacroDefs : List String -> List MacroDef
parseMacroDefs = parseMacroDefs' (NeedBegin, [])

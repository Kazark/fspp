module Fspp

%default total
%access public export

record MacroHeaderTok where
  constructor MHTok
  indent : Nat
  name : String
  args : List String

space : Nat -> Char -> Maybe Nat
space x y =
  case isSpace y of
    False => Nothing
    True => Just (x + 1)

parseHeader : Nat -> List Char -> Maybe MacroHeaderTok
parseHeader x ('/' :: '/' :: '#' :: 'd' :: 'e' :: 'f' :: 'i' :: 'n' :: 'e' :: ' ' :: cs) =
  case words $ pack cs of
    [] => Nothing
    name :: args => Just $ MHTok x name args
parseHeader _ _ = Nothing

parseHeaderTok' : Nat -> List Char -> Maybe MacroHeaderTok
parseHeaderTok' x [] = Nothing
parseHeaderTok' x (c :: cs) =
  case space x c of
    Nothing => parseHeader x (c :: cs)
    Just x => parseHeaderTok' x cs

parseHeaderTok : String -> Maybe MacroHeaderTok
parseHeaderTok = parseHeaderTok' 0 . unpack

parseFooter : String -> Bool
parseFooter = (==) "//#enddef" . trim

record MacroDef where
  constructor Define
  name : string
  args : List String
  body : List String

data ParseOneState
  = NeedDefine
  | NeedDef MacroHeaderTok (List String)

ParseState : Type
ParseState = (ParseOneState, List MacroDef)

parseMacroDefs' : List String -> List MacroDef

parseMacroDefs : List String -> List MacroDef

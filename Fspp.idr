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
  if isSpace y
  then Just (x + 1)
  else Nothing

startsWith : List Char -> List Char -> Maybe (List Char)
startsWith [] [] = Just []
startsWith [] (x :: xs) = Just (x :: xs)
startsWith (y :: xs) [] = Nothing
startsWith (y :: xs) (x :: ys) =
  if y == x
  then startsWith xs ys
  else Nothing

parseHeaderWith : String -> Nat -> List Char -> Maybe MacroHeaderTok
parseHeaderWith kw x ('/' :: '/' :: '#' :: cs) =
  startsWith (unpack kw) cs
  >>= \cs' =>
    case words $ pack cs' of
      [] => Nothing
      name :: args => Just $ MHTok x name args
parseHeaderWith _ _ _ = Nothing

parseHeaderTok' : String -> Nat -> List Char -> Maybe MacroHeaderTok
parseHeaderTok' _ x [] = Nothing
parseHeaderTok' kw x (c :: cs) =
  case space x c of
    Nothing => parseHeaderWith kw x (c :: cs)
    Just x => parseHeaderTok' kw x cs

parseHeaderTok : String -> String -> Maybe MacroHeaderTok
parseHeaderTok kw = parseHeaderTok' kw 0 . unpack

parseFooter : String -> Bool
parseFooter = (==) "//#enddef" . trim

record Macro where
  constructor Define
  name : String
  args : List String
  body : List String

data ParseOneState
  = NeedDefine
  | NeedEndDef MacroHeaderTok (List String)

ParseState : Type
ParseState = (ParseOneState, List Macro)

parseMacros' : String -> ParseState -> List String -> List Macro
parseMacros' _ (NeedDefine, macros) [] = macros
parseMacros' kw (NeedDefine, macros) (x :: xs) =
  case parseHeaderTok kw x of
    Nothing => parseMacros' kw (NeedDefine, macros) xs
    Just hd => parseMacros' kw (NeedEndDef hd [], macros) xs
parseMacros' _ (NeedEndDef _ _, macros) [] = macros
parseMacros' kw (NeedEndDef header body, macros) (x :: xs) =
  case parseFooter x of
    False => parseMacros' kw (NeedEndDef header (x :: body), macros) xs
    True  => parseMacros' kw (NeedDefine, Define (name header) (args header) body :: macros) xs

parseMacrosWith : String -> List String -> List Macro
parseMacrosWith kw = parseMacros' kw (NeedDefine, [])

parseMacrosDefine : List String -> List Macro
parseMacrosDefine = parseMacrosWith "define"

parseMacrosInvoke : List String -> List Macro
parseMacrosInvoke = parseMacrosWith "invoke"

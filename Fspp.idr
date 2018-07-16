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

parseHeader : List Char -> Maybe MacroHeaderTok
parseHeader ('/' :: '/' :: '#' :: 'd' :: 'e' :: 'f' :: ' ' :: xs) = ?parseHeader_rhs_2
parseHeader _ = Nothing

parse : Nat -> List Char -> Maybe MacroHeaderTok
parse x [] = Nothing
parse x (c :: cs) =
  case space x c of
    Nothing => ?asdf
    Just x => parse x cs

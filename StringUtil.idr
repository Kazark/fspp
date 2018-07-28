module StringUtil

%default total

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

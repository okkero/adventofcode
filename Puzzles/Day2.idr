module Puzzles.Day2


import Puzzle


%default total

isZero : (i : Int) -> Dec (i = 0)
isZero 0 = Yes Refl
isZero _ = No believe_me


safeMod : Int -> (divisor : Int) -> (Not (divisor = 0)) -> Int
safeMod dividend divisor _ =
  assert_total $ prim__sremInt dividend divisor
  
  
safeEvenDiv : Int -> (divisor : Int) -> (Not (divisor = 0)) -> Maybe Int
safeEvenDiv dividend divisor notZero =
  if safeMod dividend divisor notZero == 0 then
    Just $ assert_total $ prim__sdivInt dividend divisor
  else
    Nothing


minMax : Ord a => (ls : List a) -> {auto prf : NonEmpty ls} -> (a, a)
minMax (x :: xs) {prf = IsNonEmpty} = minMax' (x, x) xs
  where
    minMax' : Ord a => (a, a) -> List a -> (a, a)
    minMax' acc [] = acc
    minMax' (minAcc, maxAcc) (x :: xs) =
      minMax'
        ( case compare minAcc x of
               LT => minAcc
               EQ => minAcc
               GT => x
        , case compare maxAcc x of
               LT => x
               EQ => maxAcc
               GT => maxAcc
        )
        xs
    
    
findEvenDivision : List Int -> Maybe Int
findEvenDivision [] = Nothing
findEvenDivision (x :: xs) =
  case isZero x of
    Yes _ =>
      findEvenDivision xs
    
    No xContra =>
      maybe (findEvenDivision xs) Just $ find (const True) $ catMaybes $
        (\y =>
          case isZero y of
            Yes _ =>
              findEvenDivision xs
                
            No yContra =>
              maybe (safeEvenDiv y x xContra) Just (safeEvenDiv x y yContra)
        ) <$> xs


minMaxChecksum : List (List Int) -> Int
minMaxChecksum spreadsheet =
  sum $
    (\xs =>
      case nonEmpty xs of
        Yes _ =>
          let
            (min, max) = minMax xs
          in
            max - min
        No _ => 0
    ) <$> spreadsheet
    
    
evenDivisionChecksum : List (List Int) -> Int
evenDivisionChecksum spreadsheet =
  sum $ (catMaybes $ findEvenDivision <$> spreadsheet)


prepareInput : String -> List (List Int)
prepareInput input =
  (cast <$>) . words <$> lines input


solve1 : String -> String
solve1 input =
  show $ minMaxChecksum $ prepareInput input


solve2 : String -> String
solve2 input =
  show $ evenDivisionChecksum $ prepareInput input



export
puzzle : Puzzle
puzzle = MkPuzzle "Corruption Checksum" solve1 solve2

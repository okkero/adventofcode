module Day1

import Puzzle
import Data.Nat.Views


%default total


sumOffsetMatch : Nat -> List Int -> Int
sumOffsetMatch _ [] = 0
sumOffsetMatch offset ls@(_ :: _) = help (length ls) (cycle ls)
  where
    help : Nat -> (s : Stream Int) -> {default (drop offset s) offsetStream : Stream Int} -> Int
    help Z _ = 0
    help (S n) (x :: xs) {offsetStream = y :: ys} =
      help n xs {offsetStream = ys} +
        if x == y then
          x
        else
          0

sumNextMatch : List Int -> Int
sumNextMatch = sumOffsetMatch 1


sumHalfwayMatch : List Int -> Int
sumHalfwayMatch ls = sumOffsetMatch (divNatNZ (length ls) 2 SIsNotZ) ls
          
          
transformInput : String -> List Int
transformInput input =
  cast . singleton <$> unpack (trim input)
          

solve1 : String -> String
solve1 =
  show . sumNextMatch . transformInput


solve2 : String -> String
solve2 =
  show . sumHalfwayMatch . transformInput


export
puzzle : Puzzle
puzzle = MkPuzzle "Inverse Captcha" solve1 solve2

module Puzzles.Day4

import Puzzle


%default total


hasDuplicates : Eq a => List a -> Bool
hasDuplicates [] = False
hasDuplicates (x :: xs) =
  elem x xs || hasDuplicates xs


hasAnagrams : (Eq a, Ord a) => List (List a) -> Bool
hasAnagrams [] = False
hasAnagrams (x :: xs) =
  any ((== sort x) . sort) xs || hasAnagrams xs
    


solve1 : String -> String
solve1 =
  show . length . filter (not . hasDuplicates . words) . lines

solve2 : String -> String
solve2 =
  show
  . length
  . filter (not . hasAnagrams . (unpack <$>) . words)
  . lines


export
puzzle : Puzzle
puzzle = MkPuzzle "High-Entropy Passphrases" solve1 solve2

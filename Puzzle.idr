module Puzzle


public export
record Puzzle where
  constructor MkPuzzle
  name : String
  solvePart1 : String -> String
  solvePart2 : String -> String

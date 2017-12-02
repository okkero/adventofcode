module Main

import Puzzle
import Day1


puzzles : List Puzzle
puzzles =
  [ Day1.puzzle
  ]


inputDir : String
inputDir = "puzzle-input"


readInput : Nat -> IO (Either FileError String)
readInput day =
  (trim <$>) <$> (readFile $ inputDir ++ "/day" ++ show day ++ ".txt")


main : IO ()
main = do
  Right input <- readInput 1
    | Left error => (putStrLn $ show error)
  let (MkPuzzle solve1 solve2) = Day1.puzzle
  putStrLn $ solve1 input
  putStrLn $ solve2 input

module Main

import Data.Vect
import Data.Fin

import Puzzles.Day1
import Puzzles.Day2
import Puzzles.Day4
import Puzzles.Day5
import Puzzle


%default total


puzzlesCount : Nat
puzzlesCount = 5


partial
puzzles : Vect Main.puzzlesCount Puzzle
puzzles =
  [ Day1.puzzle
  , Day2.puzzle
  , MkPuzzle "_" id id
  , Day4.puzzle
  , Day5.puzzle
  ]


inputDir : String
inputDir = "puzzle-input"


readInput : Nat -> IO (Either FileError String)
readInput day =
  (trim <$>) <$> (readFile $ inputDir ++ "/day" ++ show day ++ ".txt")
  
  
showOptions : Vect n Puzzle -> IO ()
showOptions xs =
  do
    forIndexed xs $ \(dayIdx, puzzle) =>
      putStrLn $ show (S dayIdx) ++ ":\t\t" ++ name puzzle
    putStrLn "else:\t\texit"
  where
    forIndexed : {default Z idx : Nat} -> Vect n a -> ((Nat, a) -> IO ()) -> IO ()
    forIndexed [] _ = pure ()
    forIndexed {idx} (x :: xs) action =
      action (idx, x) >>= \_ => forIndexed {idx = S idx} xs action

partial
main : IO ()
main = do
  putStrLn "Advent of Code 2017 -- Solutions by okkero\n"
  showOptions puzzles
  Just (FS dayIdx) <- (\i => integerToFin i (S puzzlesCount)) . cast <$> getLine
    | Just FZ => (putStrLn "Goodbye")
    | Nothing => (putStrLn "Invalid input")
  let (MkPuzzle name solve1 solve2) = index dayIdx puzzles
  
  putStrLn $ "\n\n" ++ name
  
  Right input <- readInput (finToNat $ FS dayIdx)
    | Left error => (putStrLn $ "Error: " ++ show error)
  putStrLn $ "Part 1: " ++ solve1 input
  putStrLn $ "Part 2: " ++ solve2 input
  pure ()

module Main

import Day1


inputDir : String
inputDir = "puzzle-input"


main : IO ()
main = do
  Right input <- readFile $ inputDir ++ "/day1.txt"
    | Left error => (putStrLn $ show error)
  putStrLn $ solve1 input
  putStrLn $ solve2 input

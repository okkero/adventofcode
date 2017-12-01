module Day1

sumNextMatch : List Int -> Int
sumNextMatch [] = 0
sumNextMatch ls@(_ :: _) = help (length ls) (cycle ls)
  where
    help : Nat -> Stream Int -> Int
    help Z _ = 0
    help (S n) (x :: y :: xs) =
      help n (y :: xs) +
        if x == y then
          x
        else
          0

sumHalfwayMatch : (ls : List Int) -> Int
sumHalfwayMatch [] = 0
sumHalfwayMatch ls@(_ :: _) = help (length ls) (cycle ls)
  where
    help : Nat -> (s : Stream Int) -> {default (drop (length ls `div` 2) s) offset : Stream Int} -> Int
    help Z _ = 0
    help (S n) (x :: xs) {offset = y :: ys} =
      help n xs {offset = ys} +
        if x == y then
          x
        else
          0
          
          
prepareInput : String -> List Int
prepareInput input =
  cast . singleton <$> unpack (trim input)
          

export
solve1 : String -> String
solve1 =
  show . sumNextMatch . prepareInput


export
solve2 : String -> String
solve2 =
  show . sumHalfwayMatch . prepareInput

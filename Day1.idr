module Day1

sumNextMatch : (ls : List Int) -> Int
sumNextMatch [] = 0
sumNextMatch ls@(_ :: _) = help (length ls) (cycle ls)
  where
    help : Nat -> Stream Int -> Int
    help Z _ = 0
    help (S n) (x :: y :: xs) =
      help n xs +
        if x == y then
          x
        else
          0

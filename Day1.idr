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

export
solve : String -> String
solve input =
  show $ sumNextMatch (cast . singleton <$> unpack (trim input))

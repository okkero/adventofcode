module Puzzles.Day5

import Data.Vect
import Data.ZipVect

import Puzzle


%default total


data Instruction
  = Right Nat
  | Left Nat
  
Show Instruction where
  show (Right n) = show n
  show (Left n) = "-" ++ show (S n)
  
  
natValue : Instruction -> Nat
natValue (Right n) = n
natValue (Left n) = S n
  
  
integerToInstruction : Integer -> Instruction
integerToInstruction n =
  if n >= 0 then
    Right $ fromInteger n
  else
    Left $ fromInteger (-(n + 1))
    
    
lteToPlus : LTE n c -> (x ** n + x = c)
lteToPlus {c} LTEZero = (c ** Refl)
lteToPlus {n = S n'} {c = S c'} (LTESucc lteP) with (lteToPlus lteP)
  | (x ** refl) = (x ** eqSucc (n' + x) c' refl)


performStep : (Instruction -> Instruction) ->
              ZipVect l c Instruction ->
              Maybe (c2 ** ZipVect l c2 Instruction)
performStep {c} {l = S (c + n2)} touch (Zip xs x ys) with (x)
  | Right n with (isLTE (S (c + n)) (S (c + n2)))
    | Yes lteP = Just (_ ** jumpRight n (update touch (Zip xs x ys)))
    | No contra = Nothing
  | Left n with (isLTE (S n) c)
    | Yes lteP with (lteToPlus lteP)
      | (xx ** refl) =
          Just (xx ** jumpLeft (S n) (update touch (rewrite refl in Zip xs x ys)))
    | No contra = Nothing
    
    
prepareInput : String -> Maybe (l ** ZipVect l Z Instruction)
prepareInput input =
  case list of
    (x :: xs) => Just (_ ** fromVect $ fromList (x :: xs))
    [] => Nothing
  where
    list : List Instruction
    list = integerToInstruction . cast <$> lines input
    
    

increment : Instruction -> Instruction
increment (Right n) = Right (S n)
increment (Left (S n)) = Left n
increment (Left Z) = Right Z

decrement : Instruction -> Instruction
decrement (Right (S n)) = Right n
decrement (Right Z) = Left Z
decrement (Left n) = Left (S n)


partial
solve : (Instruction -> Instruction) -> String -> String
solve touch input with (prepareInput input)
  | Nothing = "At least one element expected"
  | Just (_ ** instructions) = show $ performSteps instructions
    where
      partial
      performSteps : {default Z acc : Nat} -> ZipVect l c Instruction -> Nat
      performSteps {acc} zv with (performStep touch zv)
        | Just (_ ** nextZV) = performSteps {acc = S acc} nextZV
        | Nothing = S acc

  
partial
solve1 : String -> String
solve1 = solve increment

partial
solve2 : String -> String
solve2 =
  solve
    (\instr =>
      case instr of
        Left n => increment instr
        Right n =>
          case isLTE 3 n of
            Yes _ => decrement instr
            No _ => increment instr
    )


export
partial
puzzle : Puzzle
puzzle = MkPuzzle "A Maze of Twisty Trampolines, All Alike" solve1 solve2

module Puzzles.Day5

import Data.Vect
import Puzzle


%default total


data ZipVect : (len : Nat) -> (cursor : Nat) -> Type -> Type where
  Zip : Vect n1 a -> a -> Vect n2 a -> ZipVect (S (n1 + n2)) n1 a
  

zipVectCursorLength : ZipVect l c a -> LT c l
zipVectCursorLength (Zip [] x ys) = LTESucc LTEZero
zipVectCursorLength (Zip (x :: xs) y ys) = LTESucc (LTESucc ?halp)

Uninhabited (ZipVect Z _ _) where
  uninhabited impossible
  
Uninhabited (ZipVect n n a) where
  uninhabited v with (zipVectCursorLength v)
    | LTEZero impossible
    | LTESucc lteP = ?a
  
  
cursor : ZipVect _ _ a -> a
cursor (Zip _ c _) = c


right : ZipVect l c a -> {auto prf : LTE (S (S c)) l} -> ZipVect l (S c) a
right {c} (Zip xs x ((::) {len} y ys)) {prf = LTESucc l} =
  rewrite sym $ plusSuccRightSucc c len in Zip (x :: xs) y ys
right (Zip xs x []) {prf} with (prf)
  | a = ?eee
--right {l} (Zip xs x []) = ?aaa
--right {c} (Zip xs x ((::) {len} y ys)) {prf = LTESucc LTEZero} = ?halp
  --Zip [] x (y :: ys) | LTESucc LTEZero = ?halp
  



solve1 : String -> String
solve2 : String -> String


export
puzzle : Puzzle
puzzle = MkPuzzle "A Maze of Twisty Trampolines, All Alike" solve1 solve2

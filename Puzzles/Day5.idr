module Puzzles.Day5

import Data.Vect
import Puzzle


%default total


data ZipVect : (len : Nat) -> (cursor : Nat) -> Type -> Type where
  Zip : Vect n1 a -> a -> Vect n2 a -> ZipVect (S (n1 + n2)) n1 a
  
  
fromVect : Vect (S n) a -> ZipVect (S n) Z a
fromVect (x :: xs) = Zip [] x xs

toVect : ZipVect l c a -> Vect l a
toVect {c} (Zip {n2} xs x ys) =
  rewrite plusSuccRightSucc c n2 in (reverse xs) ++ (x :: ys)
  

zipVectCursorLength : ZipVect l c a -> LT c l
zipVectCursorLength (Zip [] x ys) = LTESucc LTEZero
zipVectCursorLength (Zip (x :: xs) y ys) =
  LTESucc $ zipVectCursorLength (Zip xs y ys)

Uninhabited (ZipVect Z _ _) where
  uninhabited impossible
  
  
projEq : ZipVect l c a -> (n2 ** l = S (c + n2))
projEq (Zip xs x ys) = (_ ** Refl)

eqFalse : (lc = S (lc + n2)) -> Void
eqFalse {lc = Z} Refl impossible
eqFalse {lc = S lc'} prf = eqFalse (succInjective _ _ prf)

Uninhabited (ZipVect n n a) where
  uninhabited z = eqFalse $ snd $ projEq z
  
  
cursor : ZipVect _ _ a -> a
cursor (Zip _ c _) = c


succNotLessThanN : (n : Nat) -> LTE (S n) n -> Void
succNotLessThanN n LTEZero impossible
succNotLessThanN (S n) (LTESucc lteP) = succNotLessThanN n lteP

rewriteLTEPlusZeroNeutral : LTE (S m) (n + 0) -> LTE (S m) n
rewriteLTEPlusZeroNeutral {n} p = rewrite sym $ plusZeroRightNeutral n in p


right : ZipVect l c a -> {auto prf : LTE (S (S c)) l} -> ZipVect l (S c) a
right {c} (Zip xs x ((::) {len} y ys)) {prf = LTESucc l} =
  rewrite sym $ plusSuccRightSucc c len in Zip (x :: xs) y ys
right {c} (Zip xs x []) {prf = LTESucc lteP} =
  void $ succNotLessThanN c (rewriteLTEPlusZeroNeutral lteP)
  

  
left : ZipVect l (S c) a -> ZipVect l c a
left {c} (Zip {n2} (x :: xs) y ys) =
  rewrite plusSuccRightSucc c n2 in Zip xs x (y :: ys)
--todo fix it when possible: https://github.com/idris-lang/Idris-dev/issues/4250
left zv = ?left_rhs_2


update : (a -> a) -> ZipVect l c a -> ZipVect l c a
update f (Zip xs x ys) = Zip xs (f x) ys

ltePlusLeft : LTE (n + m) a -> LTE n a
ltePlusLeft {n = Z} lteP = LTEZero
ltePlusLeft {n = S n'} {m = Z} (LTESucc lteP) =
  LTESucc (rewrite sym $ plusZeroRightNeutral n' in lteP)
ltePlusLeft {n = S n'} (LTESucc lteP) = LTESucc (ltePlusLeft lteP)


jumpRight : (n : Nat) -> ZipVect l c a -> {auto prf : LTE (S (c + n)) l} -> ZipVect l (c + n) a
jumpRight {c} Z zv = rewrite plusZeroRightNeutral c in zv
jumpRight {c} (S n) zv {prf = LTESucc lteP} =
  rewrite sym $ plusSuccRightSucc c n in
    jumpRight n {prf = LTESucc reLteP}
      (right zv
        {prf = LTESucc $ ltePlusLeft {m = n} reLteP}
      )
  where
    reLteP = rewrite plusSuccRightSucc c n in lteP
  

jumpLeft : (n : Nat) -> ZipVect l (n + c) a -> ZipVect l c a
jumpLeft Z zv = zv
jumpLeft (S n) zv = jumpLeft n $ left zv


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
    

touchAtCursor : (a -> a) -> ZipVect l c a -> ZipVect l c a
touchAtCursor touch (Zip xs x ys) = Zip xs (touch x) ys
    
    
lteToPlus : LTE n c -> (x ** n + x = c)
lteToPlus {c} LTEZero = (c ** Refl)
lteToPlus {n = S n'} {c = S c'} (LTESucc lteP) with (lteToPlus lteP)
  | (x ** refl) = (x ** eqSucc (n' + x) c' refl)


performStep : (Instruction -> Instruction) ->
              ZipVect l c Instruction ->
              Maybe (c2 ** ZipVect l c2 Instruction)
performStep {c} {l = S (c + n2)} touch (Zip xs x ys) with (x)
  | Right n with (isLTE (S (c + n)) (S (c + n2)))
    | Yes lteP = Just (_ ** jumpRight n (touchAtCursor touch (Zip xs x ys)))
    | No contra = Nothing
  | Left n with (isLTE (S n) c)
    | Yes lteP with (lteToPlus lteP)
      | (xx ** refl) =
          Just (xx ** jumpLeft (S n) (touchAtCursor touch (rewrite refl in Zip xs x ys)))
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

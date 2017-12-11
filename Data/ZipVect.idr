module Data.ZipVect

import Data.Vect


%default total

export
natToFin : (bound : Nat) -> (n : Nat) -> LT n bound -> Fin bound

export
foo : (n1 : Nat) -> (n2 : Nat) -> LT n1 (S (n1 + n2))
foo Z n2 = LTESucc LTEZero
foo Z Z = LTESucc LTEZero
foo (S j) k = LTESucc $ foo j k

public export
data ZipVect : (len : Nat) -> (cursor : Fin len) -> Type -> Type where
  Zip : Vect n1 a ->
        a ->
        Vect n2 a ->
        ZipVect (S (n1 + n2)) (natToFin (S (n1 + n2)) n1 (foo n1 n2)) a
  
{-  
export
fromVect : Vect (S n) a -> ZipVect (S n) Z a
fromVect (x :: xs) = Zip [] x xs

export
toVect : ZipVect l c a -> Vect l a
toVect {c} (Zip {n2} xs x ys) =
  rewrite plusSuccRightSucc c n2 in (reverse xs) ++ (x :: ys)
  

zipVectCursorLength : ZipVect l c a -> LT c l
zipVectCursorLength (Zip [] x ys) = LTESucc LTEZero
zipVectCursorLength (Zip (x :: xs) y ys) =
  LTESucc $ zipVectCursorLength (Zip xs y ys)

public export
Uninhabited (ZipVect Z _ _) where
  uninhabited impossible
  
  
projEq : ZipVect l c a -> (n2 ** l = S (c + n2))
projEq (Zip xs x ys) = (_ ** Refl)

eqFalse : (lc = S (lc + n2)) -> Void
eqFalse {lc = Z} Refl impossible
eqFalse {lc = S lc'} prf = eqFalse (succInjective _ _ prf)

public export
Uninhabited (ZipVect n n a) where
  uninhabited z = eqFalse $ snd $ projEq z
  
export
cursor : ZipVect _ _ a -> a
cursor (Zip _ c _) = c

succNotLessThanN : (n : Nat) -> LTE (S n) n -> Void
succNotLessThanN n LTEZero impossible
succNotLessThanN (S n) (LTESucc lteP) = succNotLessThanN n lteP

rewriteLTEPlusZeroNeutral : LTE (S m) (n + 0) -> LTE (S m) n
rewriteLTEPlusZeroNeutral {n} p = rewrite sym $ plusZeroRightNeutral n in p

export
right : ZipVect l c a -> {auto prf : LTE (S (S c)) l} -> ZipVect l (S c) a
right {c} (Zip xs x ((::) {len} y ys)) {prf = LTESucc l} =
  rewrite sym $ plusSuccRightSucc c len in Zip (x :: xs) y ys
right {c} (Zip xs x []) {prf = LTESucc lteP} =
  void $ succNotLessThanN c (rewriteLTEPlusZeroNeutral lteP)

export
left : ZipVect l (S c) a -> ZipVect l c a
left {c} (Zip {n2} (x :: xs) y ys) =
  rewrite plusSuccRightSucc c n2 in Zip xs x (y :: ys)
--todo fix it when possible: https://github.com/idris-lang/Idris-dev/issues/4250
left zv = ?left_rhs_2


export
update : (a -> a) -> ZipVect l c a -> ZipVect l c a
update f (Zip xs x ys) = Zip xs (f x) ys


ltePlusLeft : LTE (n + m) a -> LTE n a
ltePlusLeft {n = Z} lteP = LTEZero
ltePlusLeft {n = S n'} {m = Z} (LTESucc lteP) =
  LTESucc (rewrite sym $ plusZeroRightNeutral n' in lteP)
ltePlusLeft {n = S n'} (LTESucc lteP) = LTESucc (ltePlusLeft lteP)


export
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
  
export
jumpLeft : (n : Nat) -> ZipVect l (n + c) a -> ZipVect l c a
jumpLeft Z zv = zv
jumpLeft (S n) zv = jumpLeft n $ left zv
-}

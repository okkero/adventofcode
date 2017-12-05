module Puzzles.Day3


%default total


shellSideLength : Nat -> Nat
shellSideLength Z = 1
shellSideLength (S n) = S (S (shellSideLength n))


shellLength : Nat -> Nat
shellLength Z = 1
shellLength (S n) = shellSideLength n * 4 + 4


getShell : Nat -> Nat


--shellSideLengthNotZ : shellSideLength n = Z -> Void
--shellSideLengthNotZ {n = Z} Refl impossible


--shellLengthNotZ : shellLength n = Z -> Void
--shellLengthNotZ Refl impossible

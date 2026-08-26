import Mathlib

namespace CryptoFrontierAtlas

abbrev BitVecN (n : Nat) := Fin n -> Bool

def boolSign (b : Bool) : Int :=
  if b then -1 else 1

def dot (x y : BitVecN n) : Bool :=
  (Finset.univ.filter fun i => x i && y i).card % 2 == 1

def walsh (f : BitVecN n -> Bool) (a : BitVecN n) : Int :=
  ∑ x, boolSign (f x != dot a x)

def hammingWeight (f : α -> Bool) [Fintype α] : Nat :=
  (Finset.univ.filter (fun x => f x = true)).card

end CryptoFrontierAtlas

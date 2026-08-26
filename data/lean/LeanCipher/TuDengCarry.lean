import LeanCipher.TuDeng
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Interval

open scoped BigOperators

namespace LeanCipher

/-!
Finite-count API for the carry distribution used by Spiegelhofer--Wallner.

For `M = 2^k - 1`, their quantity `beta_{t,k,j}` counts `a` in `[0,t]`
whose binary-weight change under addition of `M - t` is exactly the integer
`j`.  Every argument of `binaryWeightUpTo` below is at most `M`, so this is
the ordinary binary digit sum on the range used in the paper.
-/

def mersenneComplement (k t : Nat) : Nat :=
  2 ^ k - 1 - t

def binaryWeightDelta (k x y : Nat) : Int :=
  (binaryWeightUpTo k x : Int) - (binaryWeightUpTo k y : Int)

def tuDengBeta (k t : Nat) (j : Int) : Nat :=
  ((Finset.range (t + 1)).filter fun a =>
      binaryWeightDelta k (a + mersenneComplement k t) a = j).card

/- The paper sets `beta_{-1,k,j} = 0` when writing the even recurrence. -/
def tuDengBetaPred (k t : Nat) (j : Int) : Nat :=
  if t = 0 then 0 else tuDengBeta k (t - 1) j

def tuDengBetaComplementSucc (k t : Nat) (j : Int) : Nat :=
  if t < 2 ^ k - 1 then
    tuDengBeta k (mersenneComplement k (t + 1)) j
  else 0

def tuDengBetaPositiveTail (k t : Nat) : Nat :=
  (Finset.Icc 1 k).sum fun j =>
    tuDengBeta k t (j : Int) +
      tuDengBeta k (mersenneComplement k t) (-(j : Int))

end LeanCipher

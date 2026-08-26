import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Basic

open scoped BigOperators

namespace LeanCipher

/-!
Shared statement-level API for the Tu--Deng binary-string conjecture.

The representatives are the natural numbers below `2^k - 1`.  The circular
side deliberately ranges below `2^k`, so that the all-ones word is retained.
This module contains no proof of the conjecture; it is a stable semantic
prelude for bridge, carry, certificate, and root targets.
-/

def binaryBit (n i : Nat) : Nat :=
  (n / 2 ^ i) % 2

def binaryWeightUpTo (k n : Nat) : Nat :=
  (Finset.range k).sum (fun i => binaryBit n i)

def tuDengPair (k t a b : Nat) : Prop :=
  a < 2 ^ k - 1 ∧
  b < 2 ^ k - 1 ∧
  (a + b) % (2 ^ k - 1) = t % (2 ^ k - 1) ∧
  binaryWeightUpTo k a + binaryWeightUpTo k b < k

@[reducible] def tuDengPairDecidable (k t : Nat) : DecidablePred (fun p : Nat × Nat =>
    tuDengPair k t p.1 p.2) := by
  intro p
  unfold tuDengPair
  infer_instance

def tuDengCount (k t : Nat) : Nat :=
  letI : DecidablePred (fun p : Nat × Nat => tuDengPair k t p.1 p.2) :=
    tuDengPairDecidable k t
  (((Finset.range (2 ^ k - 1)).product (Finset.range (2 ^ k - 1))).filter
    (fun p : Nat × Nat => tuDengPair k t p.1 p.2)).card

theorem two_pow_sub_one_pos {k : Nat} (hk : 1 ≤ k) : 0 < 2 ^ k - 1 := by
  have hk0 : k ≠ 0 := by omega
  have : 1 < 2 ^ k := Nat.one_lt_pow hk0 (by decide)
  omega

theorem binaryBit_le_one (n i : Nat) : binaryBit n i ≤ 1 := by
  have h : binaryBit n i < 2 := by
    exact Nat.mod_lt _ (by decide)
  omega

theorem binaryWeightUpTo_le (k n : Nat) : binaryWeightUpTo k n ≤ k := by
  induction k with
  | zero => simp [binaryWeightUpTo]
  | succ k ih =>
      have hi : (Finset.range k).sum (fun i => binaryBit n i) ≤ k := by
        simpa [binaryWeightUpTo] using ih
      simp only [binaryWeightUpTo, Finset.sum_range_succ]
      have hb := binaryBit_le_one n k
      omega

theorem binaryWeightUpTo_succ_div_two
    (k n : Nat) :
    binaryWeightUpTo (k + 1) n =
      n % 2 + binaryWeightUpTo k (n / 2) := by
  induction k generalizing n with
  | zero => simp [binaryWeightUpTo, binaryBit]
  | succ k ih =>
      simp_all [binaryWeightUpTo, binaryBit, Finset.sum_range_succ,
        Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
      omega

theorem binaryWeightUpTo_all_ones (k : Nat) :
    binaryWeightUpTo k (2 ^ k - 1) = k := by
  induction k with
  | zero => simp [binaryWeightUpTo]
  | succ k ih =>
      rw [binaryWeightUpTo_succ_div_two]
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      rw [Nat.pow_succ]
      have hdecomp : 2 ^ k * 2 - 1 = (2 ^ k - 1) * 2 + 1 := by
        omega
      rw [hdecomp]
      have hdiv : ((2 ^ k - 1) * 2 + 1) / 2 = 2 ^ k - 1 := by
        rw [show (2 ^ k - 1) * 2 = 2 * (2 ^ k - 1) by
          simp [Nat.mul_comm]]
        simpa using (Nat.mul_add_div (by decide : 0 < 2) (2 ^ k - 1) 1)
      rw [hdiv, ih]
      simp [Nat.add_mod]
      omega

theorem binaryWeightUpTo_complement {k n : Nat}
    (hn : n ≤ 2 ^ k - 1) :
    binaryWeightUpTo k (2 ^ k - 1 - n) + binaryWeightUpTo k n = k := by
  induction k generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst n
      simp [binaryWeightUpTo]
  | succ k ih =>
      rw [binaryWeightUpTo_succ_div_two, binaryWeightUpTo_succ_div_two]
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
      rw [Nat.pow_succ] at hn ⊢
      have hsplit : n % 2 + 2 * (n / 2) = n := by
        simpa [Nat.mul_comm] using (Nat.mod_add_div n 2)
      have hc : 2 ^ k * 2 - 1 - n =
          2 * (2 ^ k - 1 - n / 2) + (1 - n % 2) := by
        omega
      rw [hc]
      have hpar : (1 - n % 2) < 2 := by
        have hb : n % 2 ≤ 1 :=
          Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
        omega
      have hdiv :
          (2 * (2 ^ k - 1 - n / 2) + (1 - n % 2)) / 2 =
            2 ^ k - 1 - n / 2 := by
        rw [Nat.mul_add_div (by decide : 0 < 2)]
        rw [Nat.div_eq_of_lt hpar]
        simp
      have hmod :
          (2 * (2 ^ k - 1 - n / 2) + (1 - n % 2)) % 2 =
            1 - n % 2 := by
        rw [Nat.add_mod, Nat.mul_mod]
        rw [Nat.mod_eq_of_lt hpar]
        simp
        omega
      rw [hdiv, hmod]
      have hq : n / 2 ≤ 2 ^ k - 1 := by omega
      have hi := ih hq
      omega

def circularAdd (k n t : Nat) : Nat :=
  (n + t) % (2 ^ k - 1)

def circularDecrease (k t n : Nat) : Prop :=
  binaryWeightUpTo k (circularAdd k n t) < binaryWeightUpTo k n

@[reducible] def circularDecreaseDecidable (k t : Nat) : DecidablePred (circularDecrease k t) := by
  intro n
  unfold circularDecrease circularAdd binaryWeightUpTo binaryBit
  infer_instance

def circularDecreaseCount (k t : Nat) : Nat :=
  letI : DecidablePred (circularDecrease k t) := circularDecreaseDecidable k t
  (Finset.range (2 ^ k)).filter (circularDecrease k t) |>.card

def TuDengConjecture : Prop :=
  ∀ {k t : Nat},
    2 ≤ k → 1 ≤ t → t ≤ 2 ^ k - 2 → tuDengCount k t ≤ 2 ^ (k - 1)

theorem circular_zero_not_decrease {k t : Nat} :
    ¬ circularDecrease k t 0 := by
  unfold circularDecrease circularAdd
  have hz : binaryWeightUpTo k 0 = 0 := by
    simp [binaryWeightUpTo, binaryBit]
  simp only [Nat.zero_add, hz]
  exact Nat.not_lt_zero _

end LeanCipher

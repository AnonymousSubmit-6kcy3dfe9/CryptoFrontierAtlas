import LeanCipher.BalancedEightSliceArithmetic
import LeanCipher.BalancedEightCertificates
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEightSemanticSquare

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEightRM
open LeanCipher.BalancedEightSliceArithmetic
open LeanCipher.BalancedEightCertificates

abbrev Vec := V 7

private theorem neg_natAbs_le (z : Int) : -(z.natAbs : Int) <= z := by
  have h : -z <= ((-z).natAbs : Int) := Int.le_natAbs
  rw [Int.natAbs_neg] at h
  omega

private theorem squareFirstBit_parity_iff_natAbs_eq_three_or_five
    {z : Int} (hodd : Odd z) (hbound : z.natAbs <= 9) :
    ((((z ^ 2 - 1) / 8 : Int) : ZMod 2) ≠ 0) ↔
      z.natAbs = 3 ∨ z.natAbs = 5 := by
  obtain ⟨k, hk⟩ := hodd
  have hlo := neg_natAbs_le z
  have hhi : z <= (z.natAbs : Int) := Int.le_natAbs
  have hklo : -5 <= k := by omega
  have hkhi : k <= 4 := by omega
  rw [hk]
  interval_cases k <;> norm_num <;> decide

theorem squareFirstBit_weight_eq_gamma_indicator_sum
    (g : Vec -> ZMod 2) (hg : Odd (weight g))
    (gamma : Vec -> Int)
    (habs : forall a, (gamma a).natAbs = (normalizedWalsh g a).natAbs)
    (hbound : forall a, (gamma a).natAbs <= 9) :
    (weight (intParity (squareFirstBit g)) : Int) =
      ∑ a : Vec,
        if (gamma a).natAbs = 3 ∨ (gamma a).natAbs = 5
        then (1 : Int) else 0 := by
  have hweight :
      (weight (intParity (squareFirstBit g)) : Int) =
        ∑ a : Vec,
          if intParity (squareFirstBit g) a ≠ 0 then (1 : Int) else 0 := by
    simpa [weight] using
      (Finset.sum_boole (R := Int)
        (fun a : Vec => intParity (squareFirstBit g) a ≠ 0)
        Finset.univ).symm
  rw [hweight]
  apply Finset.sum_congr rfl
  intro a _
  have hrawBound : (normalizedWalsh g a).natAbs <= 9 := by
    rw [← habs a]
    exact hbound a
  have hraw := squareFirstBit_parity_iff_natAbs_eq_three_or_five
    (normalizedWalsh_odd_of_weight_odd g hg a) hrawBound
  have hpoint :
      intParity (squareFirstBit g) a ≠ 0 ↔
        (gamma a).natAbs = 3 ∨ (gamma a).natAbs = 5 := by
    simpa only [intParity, squareFirstBit] using
      (hraw.trans (by rw [habs a]))
  simp only [hpoint]

theorem quadraticWeightSet_cast_mem_quadraticWeightsInt
    {n : Nat} (h : n ∈ quadraticWeightSet) :
    (n : Int) ∈ quadraticWeightsInt := by
  have hn :
      n = 0 ∨ n = 32 ∨ n = 48 ∨ n = 56 ∨ n = 64 ∨
        n = 72 ∨ n = 80 ∨ n = 96 ∨ n = 128 := by
    simpa [quadraticWeightSet] using h
  rcases hn with h | h | h | h | h | h | h | h | h <;>
    subst n <;> simp [quadraticWeightsInt]

theorem squareFirstBit_weight_cast_mem_quadraticWeightsInt
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) :
    (weight (intParity (squareFirstBit g)) : Int) ∈ quadraticWeightsInt := by
  obtain ⟨_, _, _, _, hweight⟩ :=
    squareFirstBit_quadratic_and_weight_mem g hg
  exact quadraticWeightSet_cast_mem_quadraticWeightsInt hweight

theorem gamma_indicator_sum_mem_quadraticWeightsInt
    (g : Vec -> ZMod 2) (hg : Odd (weight g))
    (gamma : Vec -> Int)
    (habs : forall a, (gamma a).natAbs = (normalizedWalsh g a).natAbs)
    (hbound : forall a, (gamma a).natAbs <= 9) :
    (∑ a : Vec,
        if (gamma a).natAbs = 3 ∨ (gamma a).natAbs = 5
        then (1 : Int) else 0) ∈ quadraticWeightsInt := by
  rw [← squareFirstBit_weight_eq_gamma_indicator_sum g hg gamma habs hbound]
  exact squareFirstBit_weight_cast_mem_quadraticWeightsInt g hg

end LeanCipher.BalancedEightSemanticSquare

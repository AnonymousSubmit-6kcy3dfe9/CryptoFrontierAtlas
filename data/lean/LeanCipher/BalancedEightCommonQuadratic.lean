import LeanCipher.BalancedEightLocal
import LeanCipher.BalancedEightSliceArithmetic
import LeanCipher.BalancedEightQuadratic
import Mathlib

namespace LeanCipher.BalancedEightCommonQuadratic

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEight
open LeanCipher.BalancedEightQuadratic

abbrev Vec := V 7

private theorem eight_dvd_even_frequency
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (a : Vec) :
    (8 : Int) ∣ walsh f (join a 0) := by
  rcases normalized_even_frequency_magnitude f hf hnorm hall a with h | h | h
  · have hz : walsh f (join a 0) = 0 := Int.natAbs_eq_zero.mp h
    simp [hz]
  · rcases Int.natAbs_eq_iff.mp h with h | h <;> rw [h] <;> norm_num
  · rcases Int.natAbs_eq_iff.mp h with h | h <;> rw [h] <;> norm_num

theorem oriented_normalized_sum_divisible_by_four
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell a : Vec) :
    (4 : Int) ∣
      LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
          (orientedLowerSlice f ell) a +
        LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
          (orientedUpperSlice f ell) a := by
  obtain ⟨k, hk⟩ := eight_dvd_even_frequency f hf hnorm hall a
  have hp := LeanCipher.BalancedEightSliceArithmetic.two_mul_normalizedWalsh
    (orientedLowerSlice f ell) a
  have hq := LeanCipher.BalancedEightSliceArithmetic.two_mul_normalizedWalsh
    (orientedUpperSlice f ell) a
  have hsum := oriented_slice_sum f ell a
  refine ⟨k, ?_⟩
  omega

private theorem oriented_normalized_even_magnitude
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    evenMagnitude f a = 2 *
      (LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
          (orientedLowerSlice f ell) a +
        LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
          (orientedUpperSlice f ell) a).natAbs := by
  have hp := LeanCipher.BalancedEightSliceArithmetic.two_mul_normalizedWalsh
    (orientedLowerSlice f ell) a
  have hq := LeanCipher.BalancedEightSliceArithmetic.two_mul_normalizedWalsh
    (orientedUpperSlice f ell) a
  have hsum := oriented_slice_sum f ell a
  have hscaled :
      walsh f (join a 0) = 2 *
        (LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
            (orientedLowerSlice f ell) a +
          LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
            (orientedUpperSlice f ell) a) := by
    omega
  rw [evenMagnitude, hscaled, Int.natAbs_mul]
  norm_num

private theorem oriented_normalized_odd_magnitude
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell a : Vec) :
    oddMagnitude f (a + ell) = 2 *
      (LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
          (orientedLowerSlice f ell) a -
        LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
          (orientedUpperSlice f ell) a).natAbs := by
  have hne := normalized_odd_frequency_ne_zero f hf hnorm hall (a + ell)
  have hdiff := oriented_slice_difference_abs f ell a hne
  have hp := LeanCipher.BalancedEightSliceArithmetic.two_mul_normalizedWalsh
    (orientedLowerSlice f ell) a
  have hq := LeanCipher.BalancedEightSliceArithmetic.two_mul_normalizedWalsh
    (orientedUpperSlice f ell) a
  have hscaled :
      walsh (orientedLowerSlice f ell) a -
          walsh (orientedUpperSlice f ell) a =
        2 *
          (LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
              (orientedLowerSlice f ell) a -
            LeanCipher.BalancedEightSliceArithmetic.normalizedWalsh
              (orientedUpperSlice f ell) a) := by
    omega
  rw [hscaled, Int.natAbs_mul] at hdiff
  norm_num at hdiff
  exact hdiff.symm

private theorem product_first_bit_parity_arithmetic
    {p q : Int} {even odd : Nat}
    (heq : even = 2 * (p + q).natAbs)
    (hoq : odd = 2 * (p - q).natAbs)
    (heven : even = 0 ∨ even = 8 ∨ even = 16)
    (hodd : odd = 4 ∨ odd = 12 ∨ odd = 20) :
    ((((p * q + 1) / 4 : Int) : ZMod 2)) =
      if even = 8 then 1 else 0 := by
  have hsabs : (p + q).natAbs = even / 2 := by omega
  have hdabs : (p - q).natAbs = odd / 2 := by omega
  have hsquare :
      (p + q) ^ 2 = (((even / 2 : Nat) : Int) ^ 2) := by
    rw [← Int.natAbs_sq, hsabs]
  have hdsquare :
      (p - q) ^ 2 = (((odd / 2 : Nat) : Int) ^ 2) := by
    rw [← Int.natAbs_sq, hdabs]
  have hfour :
      4 * (p * q) =
        ((even / 2 : Nat) : Int) ^ 2 -
          ((odd / 2 : Nat) : Int) ^ 2 := by
    nlinarith [hsquare, hdsquare]
  have hpq :
      p * q =
        (((even / 2 : Nat) : Int) ^ 2 -
          ((odd / 2 : Nat) : Int) ^ 2) / 4 := by
    rw [← hfour]
    omega
  rcases heven with rfl | rfl | rfl <;>
    rcases hodd with rfl | rfl | rfl <;>
    norm_num [hpq] <;> native_decide

theorem product_first_bit_eq_even_magnitude_indicator
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell a : Vec) :
    LeanCipher.BalancedEightRM.intParity
        (LeanCipher.BalancedEightSliceArithmetic.productFirstBit
          (orientedLowerSlice f ell) (orientedUpperSlice f ell)) a =
      if evenMagnitude f a = 8 then 1 else 0 := by
  apply product_first_bit_parity_arithmetic
  · exact oriented_normalized_even_magnitude f ell a
  · exact oriented_normalized_odd_magnitude f hf hnorm hall ell a
  · exact normalized_even_frequency_magnitude f hf hnorm hall a
  · exact normalized_odd_frequency_magnitude f hf hnorm hall (a + ell)

private theorem oriented_slice_weights_odd
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell : Vec) :
    Odd (weight (orientedLowerSlice f ell)) ∧
      Odd (weight (orientedUpperSlice f ell)) := by
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h
  · rw [h.2.1, h.2.2]
    norm_num
  · rw [h.2.1, h.2.2]
    norm_num
  · rw [h.2.1, h.2.2]
    norm_num

theorem exists_common_quadratic
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) :
    ∃ R : RM2 7, ∀ a : Vec,
      rm2Eval R a = if evenMagnitude f a = 8 then 1 else 0 := by
  let ell : Vec := 0
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have hodd := oriented_slice_weights_odd f hf hnorm hall ell
  obtain ⟨Q, linear, constant, hrepresentation, _hweight⟩ :=
    LeanCipher.BalancedEightSliceArithmetic.productFirstBit_quadratic_and_weight_mem
      g h hodd.1 hodd.2
      (oriented_normalized_sum_divisible_by_four f hf hnorm hall ell)
  have hzeroIndicator :
      (if evenMagnitude f (0 : Vec) = 8 then (1 : ZMod 2) else 0) = 0 := by
    have hjoin : join (0 : Vec) 0 = (0 : V 8) := by native_decide
    have hzero : walsh f (join (0 : Vec) 0) = 0 := by
      rw [hjoin, walsh_zero_of_balanced f hf]
    simp [evenMagnitude, hzero]
  have hconstant : constant = 0 := by
    have hreprZero := hrepresentation (0 : Vec)
    have hproductZero :=
      product_first_bit_eq_even_magnitude_indicator
        f hf hnorm hall ell (0 : Vec)
    rw [hzeroIndicator] at hproductZero
    rw [hproductZero] at hreprZero
    simpa [LeanCipher.BalancedEightRM.quadraticEval] using hreprZero.symm
  let R : RM2 7 := { quadratic := Q, linear := linear }
  refine ⟨R, ?_⟩
  intro a
  have hrepr := hrepresentation a
  have hproduct := product_first_bit_eq_even_magnitude_indicator
    f hf hnorm hall ell a
  rw [hproduct] at hrepr
  calc
    rm2Eval R a = LeanCipher.BalancedEightRM.quadraticEval
        Q linear constant a := by
      simp only [R, rm2Eval, quadraticEval,
        LeanCipher.BalancedEightRM.quadraticEval, f2Dot,
        hconstant]
      ac_rfl
    _ = (if evenMagnitude f a = 8 then 1 else 0) := hrepr.symm

end LeanCipher.BalancedEightCommonQuadratic

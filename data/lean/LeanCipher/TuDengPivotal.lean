import Mathlib

open Set MeasureTheory
open scoped BigOperators intervalIntegral

namespace LeanCipher

/-!
  Numerical core of the pivotal-integral argument for the Tu--Deng family.

  The combinatorial P4--P7 classification supplies the natural numbers
  `h`, `u`, `r`, and `p0` below:

  * `h` is the positive rank excess of the upper carry word;
  * `u` is the number of mismatch positions;
  * `r` is the number of mismatch positions whose outgoing carry is one;
  * `p0` counts the forced zero bits in the first `h - 1` positions.

  The cyclic telescoping identity is `hTel : 2 * r = u + h` (P8), while
  `hp0 : p0 <= h - 1` is the interval bound (P9).  This module proves the
  resulting fixed-bit balance and the non-negativity of each biased profile
  (P10).  It intentionally does not assert the missing P4/P5 classification
  or the all-parameter Tu--Deng theorem.
-/

/-!
  P8--P9: fixed-bit balance.  The second conclusion is the side condition
  needed to use `Nat.sub_eq_iff_eq_add`; retaining it explicitly prevents
  accidental reasoning with truncated natural subtraction.
-/
theorem tuDeng_pivotal_profile_balance
    (h u r p0 : Nat)
    (hTel : 2 * r = u + h)
    (hr : 1 <= r)
    (hh : 1 <= h)
    (hru : r <= u)
    (hp0 : p0 <= h - 1) :
    (r - 1) - (u - r + p0) = h - 1 - p0 ∧
      u - r + p0 <= r - 1 := by
  constructor
  · omega
  · have hur : u - r = r - h := by omega
    have hhr : h <= r := by omega
    rw [hur]
    calc
      r - h + p0 <= r - h + (h - 1) :=
        Nat.add_le_add_left hp0 (r - h)
      _ = r - 1 := by omega

/-!
  P10: for `0 <= p <= 1/2`, a profile with at least as many fixed ones as
  fixed zeros dominates its complementary profile.  The proof factors out
  the common `p^b (1-p)^b` term and uses monotonicity of powers.
-/
theorem tuDeng_biased_integrand_nonneg
    {a b : Nat} (hab : b <= a) {p : ℝ}
    (hp : p ∈ Set.Icc 0 (1 / 2)) :
    0 <= (1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b := by
  have hp0 : 0 <= p := hp.1
  have hhalf : p <= 1 / 2 := hp.2
  have hcomp : p <= 1 - p := by linarith
  have h1p : 0 <= 1 - p := by linarith
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  have hpow : p ^ d <= (1 - p) ^ d := by
    exact pow_le_pow_left₀ hp0 hcomp d
  have hcommon : 0 <= (1 - p) ^ b * p ^ b := by
    exact mul_nonneg (pow_nonneg h1p b) (pow_nonneg hp0 b)
  have hmul :
      (1 - p) ^ b * p ^ b * p ^ d <=
        (1 - p) ^ b * p ^ b * (1 - p) ^ d := by
    exact mul_le_mul_of_nonneg_left hpow hcommon
  have hleft :
      p ^ a * (1 - p) ^ b =
        (1 - p) ^ b * p ^ b * p ^ d := by
    rw [hd, pow_add]
    ring
  have hright :
      (1 - p) ^ b * p ^ b * (1 - p) ^ d =
        (1 - p) ^ a * p ^ b := by
    rw [hd, pow_add]
    ring
  rw [sub_nonneg]
  rw [hleft, ← hright]
  exact hmul

/-! The integral form used when summing all pivotal groups. -/
theorem tuDeng_biased_integral_nonneg
    (a b : Nat) (hab : b <= a) :
    0 <= ∫ p : ℝ in (0 : ℝ)..(1 / 2),
      ((1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b) := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro p hp
  exact tuDeng_biased_integrand_nonneg hab hp

end LeanCipher

import LeanCipher.BooleanWalsh
import LeanCipher.BooleanNonlinearity
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh

/-!
# The spectral core of the balanced eight-variable problem

This file contains no finite classification data.  It establishes the first
reduction in the paper directly for an arbitrary Boolean function: a balanced
eight-variable function has four-divisible Walsh coefficients, Parseval forces
a coefficient of magnitude at least `20`, and nonlinearity above `116` would
force every coefficient to have magnitude at most `20`.
-/

abbrev maximumWalshMagnitude (f : V n -> ZMod 2) : Nat :=
  LeanCipher.BooleanNonlinearity.maximumWalshMagnitude f

abbrev nonlinearity (f : V n -> ZMod 2) : Nat :=
  LeanCipher.BooleanNonlinearity.nonlinearity f

theorem nonlinearity_eq_paper_formula
    (f : V n -> ZMod 2) (hn : 1 <= n) :
    nonlinearity f = 2 ^ (n - 1) - maximumWalshMagnitude f / 2 := by
  exact LeanCipher.BooleanNonlinearity.nonlinearity_eq_paper_formula f hn

theorem walsh_natAbs_le_maximum (f : V n -> ZMod 2) (a : V n) :
    (walsh f a).natAbs <= maximumWalshMagnitude f := by
  exact Finset.le_sup (s := (Finset.univ : Finset (V n)))
    (f := fun b => (walsh f b).natAbs) (Finset.mem_univ a)

theorem walsh_zero_eq_card_sub_two_weight (f : V n -> ZMod 2) :
    walsh f 0 = (2 : Int) ^ n - 2 * (weight f : Int) := by
  simpa using walsh_eq_card_sub_two_mul_weight f 0

theorem walsh_zero_of_balanced (f : V 8 -> ZMod 2)
    (hf : weight f = 128) : walsh f 0 = 0 := by
  rw [walsh_zero_eq_card_sub_two_weight, hf]
  norm_num

theorem four_dvd_all_walsh_of_balanced (f : V 8 -> ZMod 2)
    (hf : weight f = 128) (a : V 8) : (4 : Int) ∣ walsh f a := by
  apply four_dvd_walsh_of_weight_even f a (by norm_num)
  rw [hf]
  norm_num

private theorem natAbs_le_sixteen_of_four_dvd_of_lt_twenty
    {z : Int} (hdiv : (4 : Int) ∣ z) (hlt : z.natAbs < 20) :
    z.natAbs <= 16 := by
  obtain ⟨q, rfl⟩ := hdiv
  rw [Int.natAbs_mul]
  norm_num at hlt ⊢
  omega

private theorem int_sq_le_256_of_natAbs_le_16
    {z : Int} (hz : z.natAbs <= 16) : z ^ 2 <= 256 := by
  have habs : |z| <= 16 := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hz
  have hs : |z| ^ 2 <= (16 : Int) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg z) (by norm_num)).2 habs
  simpa using hs

theorem exists_walsh_magnitude_at_least_twenty
    (f : V 8 -> ZMod 2) (hf : weight f = 128) :
    exists a : V 8, 20 <= (walsh f a).natAbs := by
  by_contra h
  push Not at h
  have hzero : walsh f 0 = 0 := walsh_zero_of_balanced f hf
  have hterm (a : V 8) :
      walsh f a ^ 2 <= if a = 0 then 0 else 256 := by
    by_cases ha : a = 0
    · subst a
      simp [hzero]
    · rw [if_neg ha]
      exact int_sq_le_256_of_natAbs_le_16
        (natAbs_le_sixteen_of_four_dvd_of_lt_twenty
          (four_dvd_all_walsh_of_balanced f hf a) (h a))
  have hsum :
      (∑ a : V 8, walsh f a ^ 2) <=
        ∑ a : V 8, if a = 0 then (0 : Int) else 256 := by
    exact Finset.sum_le_sum fun a _ => hterm a
  have hrhs : (∑ a : V 8, if a = 0 then (0 : Int) else 256) = 65280 := by
    classical
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.univ.filter fun x : V 8 => x ≠ 0) =
        Finset.univ.erase 0 by
      simpa only [ne_eq] using Finset.filter_ne' (Finset.univ : Finset (V 8)) 0]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]
    norm_num [f2Vec_card]
  rw [walsh_parseval f, hrhs] at hsum
  norm_num at hsum

theorem maximumWalshMagnitude_lt_twenty_four_of_nonlinearity_gt_116
    (f : V 8 -> ZMod 2) (hNL : 116 < nonlinearity f) :
    maximumWalshMagnitude f < 24 := by
  unfold nonlinearity at hNL
  change 116 < (2 ^ 8 - maximumWalshMagnitude f) / 2 at hNL
  have hcard : maximumWalshMagnitude f <= 2 ^ 8 :=
    LeanCipher.BooleanNonlinearity.maximumWalshMagnitude_le_card f
  by_contra hnot
  have hge : 24 <= maximumWalshMagnitude f := Nat.not_lt.mp hnot
  have hsub : 2 ^ 8 - maximumWalshMagnitude f <= 2 ^ 8 - 24 :=
    Nat.sub_le_sub_left hge (2 ^ 8)
  have hle : (2 ^ 8 - maximumWalshMagnitude f) / 2 <= 116 := by
    apply Nat.div_le_of_le_mul
    norm_num at hsub ⊢
    omega
  exact (Nat.not_lt_of_ge hle hNL).elim

theorem hypothetical_spectrum_bounds
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hNL : 116 < nonlinearity f) :
    (forall a : V 8, (walsh f a).natAbs <= 20) ∧
      exists a : V 8, (walsh f a).natAbs = 20 := by
  have hmax := maximumWalshMagnitude_lt_twenty_four_of_nonlinearity_gt_116 f hNL
  have hall : forall a : V 8, (walsh f a).natAbs <= 20 := by
    intro a
    have hlt : (walsh f a).natAbs < 24 :=
      (walsh_natAbs_le_maximum f a).trans_lt hmax
    obtain ⟨q, hq⟩ := four_dvd_all_walsh_of_balanced f hf a
    rw [hq, Int.natAbs_mul] at hlt ⊢
    norm_num at hlt ⊢
    omega
  refine ⟨hall, ?_⟩
  obtain ⟨a, ha⟩ := exists_walsh_magnitude_at_least_twenty f hf
  exact ⟨a, Nat.le_antisymm (hall a) ha⟩

def supportXor (f : V n -> ZMod 2) : V n :=
  ∑ x, f x • x

def supportIntersection (f : V n -> ZMod 2) (a : V n) : Nat :=
  ((Finset.univ : Finset (V n)).filter fun x =>
    f x ≠ 0 ∧ f2Dot a x ≠ 0).card

theorem f2Dot_supportXor (f : V n -> ZMod 2) (a : V n) :
    f2Dot a (supportXor f) =
      ∑ x, f x * f2Dot a x := by
  classical
  calc
    f2Dot a (supportXor f) = ∑ i, a i * (∑ x, f x * x i) := by
      simp [f2Dot, supportXor]
    _ = ∑ i, ∑ x, a i * (f x * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ x, ∑ i, a i * (f x * x i) := Finset.sum_comm
    _ = ∑ x, f x * f2Dot a x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [f2Dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

private theorem support_character_sum
    (f : V n -> ZMod 2) (a : V n) :
    (∑ x ∈ (Finset.univ : Finset (V n)).filter (fun x => f x ≠ 0),
        character a x) =
      (weight f : Int) - 2 * (supportIntersection f a : Int) := by
  classical
  let S := (Finset.univ : Finset (V n)).filter fun x => f x ≠ 0
  let T := S.filter fun x => f2Dot a x ≠ 0
  have hT : T.card = supportIntersection f a := by
    simp only [T, S, supportIntersection]
    congr 1
    ext x
    simp
  have hS : S.card = weight f := by rfl
  change S.sum (fun x => character a x) = _
  calc
    S.sum (fun x => character a x) =
        S.sum (fun x => (1 : Int) -
          2 * if f2Dot a x ≠ 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rcases zmod2_eq_zero_or_one (f2Dot a x) with hx | hx
      · simp [character, hx]
      · simp [character, hx]
    _ = (S.card : Int) - 2 * (T.card : Int) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hindicator :
          (∑ x ∈ S, if f2Dot a x ≠ 0 then (1 : Int) else 0) =
            (T.card : Int) := by
        simpa only [T] using
          Finset.sum_boole (R := Int) (fun x => f2Dot a x ≠ 0) S
      rw [hindicator]
      simp
    _ = (weight f : Int) - 2 * (supportIntersection f a : Int) := by
      rw [hS, hT]

theorem walsh_eq_neg_two_support_character_sum_of_ne_zero
    (f : V n -> ZMod 2) (a : V n) (ha : a ≠ 0) :
    walsh f a = -2 *
      ∑ x ∈ (Finset.univ : Finset (V n)).filter (fun x => f x ≠ 0),
        character a x := by
  classical
  rw [walsh_eq_sum_sign_mul_character]
  have hchar : (∑ x : V n, character a x) = 0 := by
    simpa [ha] using character_sum a
  calc
    (∑ x : V n, sign (f x) * character a x) =
        ∑ x : V n,
          (character a x - 2 * if f x ≠ 0 then character a x else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [sign_eq_one_sub_two_indicator]
            split_ifs <;> ring
    _ = (∑ x : V n, character a x) -
        2 * ∑ x : V n, if f x ≠ 0 then character a x else 0 := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ x : V n, character a x) -
        2 * ∑ x ∈ (Finset.univ : Finset (V n)).filter (fun x => f x ≠ 0),
          character a x := by
          congr 1
          rw [Finset.sum_ite]
          simp
    _ = _ := by rw [hchar]; ring

theorem walsh_support_intersection_formula
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (a : V 8) (ha : a ≠ 0) :
    walsh f a = -256 + 4 * (supportIntersection f a : Int) := by
  rw [walsh_eq_neg_two_support_character_sum_of_ne_zero f a ha,
    support_character_sum, hf]
  ring

theorem supportIntersection_cast_eq_dot (f : V n -> ZMod 2) (a : V n) :
    (supportIntersection f a : ZMod 2) = f2Dot a (supportXor f) := by
  rw [f2Dot_supportXor]
  classical
  symm
  calc
    (∑ x : V n, f x * f2Dot a x) =
        ∑ x : V n, if f x ≠ 0 ∧ f2Dot a x ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hf0 : f x = 0
      · simp [hf0]
      · have hf1 := zmod2_eq_one_of_ne_zero hf0
        by_cases hd0 : f2Dot a x = 0
        · simp [hf0, hd0]
        · have hd1 := zmod2_eq_one_of_ne_zero hd0
          simp [hf1, hd1]
    _ = (supportIntersection f a : ZMod 2) := by
      simp [supportIntersection, Finset.sum_boole]

theorem normalized_walsh_parity
    (f : V 8 -> ZMod 2) (hf : weight f = 128) (a : V 8) :
    ((walsh f a / 4 : Int) : ZMod 2) = f2Dot a (supportXor f) := by
  by_cases ha : a = 0
  · subst a
    simp [walsh_zero_of_balanced f hf]
  · rw [walsh_support_intersection_formula f hf a ha]
    have hdiv : (-256 + 4 * (supportIntersection f a : Int)) / 4 =
        -64 + (supportIntersection f a : Int) := by omega
    rw [hdiv]
    rw [Int.cast_add]
    have h64 : ((-64 : Int) : ZMod 2) = 0 := by native_decide
    rw [h64, zero_add]
    exact supportIntersection_cast_eq_dot f a

theorem supportXor_ne_zero_of_hypothetical
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20) :
    supportXor f ≠ 0 := by
  intro hc
  obtain ⟨a, ha⟩ := exists_walsh_magnitude_at_least_twenty f hf
  have hwa : (walsh f a).natAbs = 20 := Nat.le_antisymm (hall a) ha
  obtain ⟨q, hq⟩ := four_dvd_all_walsh_of_balanced f hf a
  have hqabs : q.natAbs = 5 := by
    rw [hq, Int.natAbs_mul] at hwa
    norm_num at hwa
    omega
  have hodd : ((walsh f a / 4 : Int) : ZMod 2) = 1 := by
    rw [hq]
    have hcancel : (4 * q : Int) / 4 = q := by omega
    rw [hcancel]
    have : (q : ZMod 2) = 1 := by
      rcases Int.natAbs_eq_iff.mp hqabs with hq | hq
      · subst q
        native_decide
      · subst q
        native_decide
    exact this
  have hpar := normalized_walsh_parity f hf a
  rw [hc, f2Dot_zero_right] at hpar
  exact zero_ne_one (hpar.symm.trans hodd)

end LeanCipher.BalancedEight

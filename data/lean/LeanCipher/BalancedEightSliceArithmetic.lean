import LeanCipher.BalancedEightRM
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEightSliceArithmetic

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEightRM

abbrev Vec := V 7

/-! Integer normalizations and correlation functions for seven-variable slices. -/

def normalizedWalsh (g : Vec -> ZMod 2) (a : Vec) : Int :=
  64 - (weight fun x => g x + f2Dot a x : Int)

def translate (g : Vec -> ZMod 2) (t : Vec) : Vec -> ZMod 2 :=
  fun x => g (x + t)

def autocorrelation (g : Vec -> ZMod 2) (t : Vec) : Int :=
  ∑ x, sign (g x + g (x + t))

def crossCorrelation (g h : Vec -> ZMod 2) (t : Vec) : Int :=
  ∑ x, sign (g x + h (x + t))

def supportOverlap (g : Vec -> ZMod 2) (t : Vec) : Nat :=
  ((Finset.univ : Finset Vec).filter fun x =>
    g x ≠ 0 ∧ g (x + t) ≠ 0).card

def productFirstBit (g h : Vec -> ZMod 2) (a : Vec) : Int :=
  (normalizedWalsh g a * normalizedWalsh h a + 1) / 4

def squareFirstBit (g : Vec -> ZMod 2) (a : Vec) : Int :=
  (normalizedWalsh g a ^ 2 - 1) / 8

def pointMassZero (a : Vec) : Int :=
  if a = 0 then 1 else 0

def correctedSquareFirstBit (g : Vec -> ZMod 2) (a : Vec) : Int :=
  squareFirstBit g a - 16 * pointMassZero a

theorem two_mul_normalizedWalsh (g : Vec -> ZMod 2) (a : Vec) :
    2 * normalizedWalsh g a = walsh g a := by
  rw [walsh_eq_card_sub_two_mul_weight]
  simp only [normalizedWalsh]
  norm_num
  ring

theorem normalizedWalsh_eq_walsh_div_two (g : Vec -> ZMod 2) (a : Vec) :
    normalizedWalsh g a = walsh g a / 2 := by
  rw [← two_mul_normalizedWalsh g a]
  omega

theorem normalizedWalsh_odd_of_weight_odd
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) (a : Vec) :
    Odd (normalizedWalsh g a) := by
  have hlinear : Even (weight fun x : Vec => f2Dot a x) :=
    linear_weight_even a (by norm_num)
  have hshift : Odd (weight fun x => g x + f2Dot a x) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hiff := (weight_add_even_iff g (fun x => f2Dot a x)).mp heven
    exact (Nat.not_even_iff_odd.mpr hg) (hiff.mpr hlinear)
  obtain ⟨r, hr⟩ := hshift
  refine ⟨31 - (r : Int), ?_⟩
  simp only [normalizedWalsh]
  push_cast [hr]
  ring

theorem normalizedWalsh_parseval (g : Vec -> ZMod 2) :
    (∑ a : Vec, normalizedWalsh g a ^ 2) = 4096 := by
  have hpoint (a : Vec) :
      walsh g a ^ 2 = 4 * normalizedWalsh g a ^ 2 := by
    rw [← two_mul_normalizedWalsh]
    ring
  have hsum :
      (∑ a : Vec, walsh g a ^ 2) =
        4 * ∑ a : Vec, normalizedWalsh g a ^ 2 := by
    calc
      (∑ a : Vec, walsh g a ^ 2) =
          ∑ a : Vec, 4 * normalizedWalsh g a ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            exact hpoint a
      _ = 4 * ∑ a : Vec, normalizedWalsh g a ^ 2 := by
            rw [Finset.mul_sum]
  rw [walsh_parseval] at hsum
  norm_num at hsum
  omega

@[simp] theorem translate_zero (g : Vec -> ZMod 2) : translate g 0 = g := by
  funext x
  simp [translate]

theorem translate_add_self (g : Vec -> ZMod 2) (t x : Vec) :
    translate g t (x + t) = g x := by
  simp [translate, add_assoc, LeanCipher.f2vec_add_self]

theorem weight_translate (g : Vec -> ZMod 2) (t : Vec) :
    weight (translate g t) = weight g := by
  classical
  unfold weight translate
  apply Finset.card_bijective (fun x : Vec => x + t)
  · exact (Equiv.addRight t).bijective
  · intro x
    simp

@[simp] theorem autocorrelation_zero (g : Vec -> ZMod 2) :
    autocorrelation g 0 = 128 := by
  calc
    autocorrelation g 0 = ∑ x : Vec, sign (g x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      simp [pow_two]
    _ = 128 := by simp

theorem crossCorrelation_eq_card_sub_two_weight
    (g h : Vec -> ZMod 2) (t : Vec) :
    crossCorrelation g h t =
      128 - 2 * (weight fun x => g x + translate h t x : Int) := by
  simpa [crossCorrelation, translate] using
    (sum_sign_eq_card_sub_two_mul_weight
      (fun x : Vec => g x + translate h t x))

theorem four_dvd_crossCorrelation_of_odd_weights
    (g h : Vec -> ZMod 2) (hg : Odd (weight g)) (hh : Odd (weight h))
    (t : Vec) :
    (4 : Int) ∣ crossCorrelation g h t := by
  have hhTranslate : Odd (weight (translate h t)) := by
    rw [weight_translate]
    exact hh
  have hEven : Even (weight fun x => g x + translate h t x) := by
    rw [weight_add_even_iff]
    constructor
    · intro hgEven
      exact ((Nat.not_even_iff_odd.mpr hg) hgEven).elim
    · intro hhEven
      exact ((Nat.not_even_iff_odd.mpr hhTranslate) hhEven).elim
  obtain ⟨r, hr⟩ := hEven
  refine ⟨32 - r, ?_⟩
  rw [crossCorrelation_eq_card_sub_two_weight, hr]
  push_cast
  ring

private theorem overlap_indicator_sum
    (g : Vec -> ZMod 2) (t : Vec) :
    (∑ x : Vec, g x * g (x + t)) = (supportOverlap g t : ZMod 2) := by
  classical
  calc
    (∑ x : Vec, g x * g (x + t)) =
        ∑ x : Vec,
          if g x ≠ 0 ∧ g (x + t) ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases zmod2_eq_zero_or_one (g x) with hx | hx <;>
        rcases zmod2_eq_zero_or_one (g (x + t)) with hy | hy <;>
        simp [hx, hy]
    _ = (supportOverlap g t : ZMod 2) := by
      simp [supportOverlap, Finset.sum_boole]

private theorem overlap_sum_eq_zero_of_ne_zero
    (g : Vec -> ZMod 2) {t : Vec} (ht : t ≠ 0) :
    (∑ x : Vec, g x * g (x + t)) = 0 := by
  obtain ⟨a, ha⟩ := f2Dot_right_surjective ht (1 : ZMod 2)
  let P : Vec -> ZMod 2 := fun x => g x * g (x + t)
  have hP (x : Vec) : P (x + t) = P x := by
    simp only [P, add_assoc, LeanCipher.f2vec_add_self, add_zero]
    ring
  have hsplit (x : Vec) :
      P x = P x * f2Dot a x + P x * f2Dot a (x + t) := by
    change f2Dot a t = 1 at ha
    rw [f2Dot_add_right, ha]
    rcases zmod2_eq_zero_or_one (f2Dot a x) with hx | hx <;>
      simp [hx, CharTwo.add_self_eq_zero]
  have hreindex :
      (∑ x : Vec, P x * f2Dot a (x + t)) =
        ∑ x : Vec, P x * f2Dot a x := by
    exact Fintype.sum_equiv (Equiv.addRight t)
      (fun x : Vec => P x * f2Dot a (x + t))
      (fun x : Vec => P x * f2Dot a x)
      (fun x => by
        simpa [add_comm] using
          congrArg (fun z => z * f2Dot a (x + t)) (hP x).symm)
  calc
    (∑ x : Vec, g x * g (x + t)) = ∑ x : Vec, P x := by rfl
    _ = ∑ x : Vec,
          (P x * f2Dot a x + P x * f2Dot a (x + t)) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hsplit x
    _ = (∑ x : Vec, P x * f2Dot a x) +
          ∑ x : Vec, P x * f2Dot a (x + t) := by
          rw [Finset.sum_add_distrib]
    _ = 0 := by rw [hreindex, CharTwo.add_self_eq_zero]

theorem supportOverlap_even_of_ne_zero
    (g : Vec -> ZMod 2) {t : Vec} (ht : t ≠ 0) :
    Even (supportOverlap g t) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  rw [← overlap_indicator_sum]
  exact overlap_sum_eq_zero_of_ne_zero g ht

theorem autocorrelation_support_formula (g : Vec -> ZMod 2) (t : Vec) :
    autocorrelation g t =
      128 - 4 * (weight g : Int) + 4 * (supportOverlap g t : Int) := by
  classical
  have hshiftIndicator :
      (∑ x : Vec, if g (x + t) ≠ 0 then (1 : Int) else 0) =
        (weight g : Int) := by
    calc
      (∑ x : Vec, if g (x + t) ≠ 0 then (1 : Int) else 0) =
          ∑ x : Vec, if g x ≠ 0 then (1 : Int) else 0 := by
            exact Fintype.sum_equiv (Equiv.addRight t)
              (fun x : Vec => if g (x + t) ≠ 0 then (1 : Int) else 0)
              (fun x : Vec => if g x ≠ 0 then (1 : Int) else 0)
              (fun _ => rfl)
      _ = (weight g : Int) := by
            simpa [weight] using
              Finset.sum_boole (R := Int) (fun x : Vec => g x ≠ 0) Finset.univ
  have hoverlapIndicator :
      (∑ x : Vec,
        (if g x ≠ 0 then (1 : Int) else 0) *
          if g (x + t) ≠ 0 then (1 : Int) else 0) =
        (supportOverlap g t : Int) := by
    calc
      _ = ∑ x : Vec,
          if g x ≠ 0 ∧ g (x + t) ≠ 0 then (1 : Int) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : g x = 0 <;> by_cases hy : g (x + t) = 0 <;>
              simp [hx, hy]
      _ = (supportOverlap g t : Int) := by
            simp [supportOverlap, Finset.sum_boole]
  have hweightIndicator :
      (∑ x : Vec, if g x ≠ 0 then (1 : Int) else 0) =
        (weight g : Int) := by
    simpa [weight] using
      Finset.sum_boole (R := Int) (fun x : Vec => g x ≠ 0) Finset.univ
  calc
    autocorrelation g t =
        ∑ x : Vec, sign (g x) * sign (g (x + t)) := by
          apply Finset.sum_congr rfl
          intro x _
          simp
    _ = ∑ x : Vec,
        ((1 : Int) - 2 * if g x ≠ 0 then 1 else 0) *
          ((1 : Int) - 2 * if g (x + t) ≠ 0 then 1 else 0) := by
          simp_rw [sign_eq_one_sub_two_indicator]
    _ = ∑ x : Vec,
        ((1 : Int) - 2 * (if g x ≠ 0 then 1 else 0) -
          2 * (if g (x + t) ≠ 0 then 1 else 0) +
          4 * ((if g x ≠ 0 then 1 else 0) *
            if g (x + t) ≠ 0 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = 128 - 2 *
          (∑ x : Vec, if g x ≠ 0 then (1 : Int) else 0) -
        2 * (∑ x : Vec, if g (x + t) ≠ 0 then (1 : Int) else 0) +
        4 * (∑ x : Vec,
          (if g x ≠ 0 then (1 : Int) else 0) *
            if g (x + t) ≠ 0 then (1 : Int) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Finset.mul_sum]
          rw [f2Vec_card]
          norm_num
    _ = _ := by rw [hweightIndicator, hshiftIndicator, hoverlapIndicator]; ring

theorem four_mul_autocorrelationQuarter
    (g : Vec -> ZMod 2) (t : Vec) :
    4 * (autocorrelation g t / 4) = autocorrelation g t := by
  rw [autocorrelation_support_formula]
  omega

theorem autocorrelation_div_four_eq
    (g : Vec -> ZMod 2) (t : Vec) :
    autocorrelation g t / 4 =
      32 - (weight g : Int) + (supportOverlap g t : Int) := by
  rw [autocorrelation_support_formula]
  omega

theorem autocorrelation_div_four_odd_of_weight_odd
    (g : Vec -> ZMod 2) (hg : Odd (weight g))
    {t : Vec} (ht : t ≠ 0) :
    Odd (autocorrelation g t / 4) := by
  rw [autocorrelation_div_four_eq]
  obtain ⟨r, hr⟩ := hg
  obtain ⟨s, hs⟩ := supportOverlap_even_of_ne_zero g ht
  refine ⟨15 - r + s, ?_⟩
  push_cast [hr, hs]
  ring

/-! Wiener--Khinchin identities in the normalization used by the slices. -/

theorem hadamard_walsh_product
    (g h : Vec -> ZMod 2) (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        (fun a => walsh g a * walsh h a) t =
      128 * crossCorrelation g h t := by
  classical
  simp only [hadamardTransform]
  simp_rw [walsh_eq_sum_sign_mul_character]
  calc
    (∑ a : Vec, character t a *
        ((∑ x : Vec, sign (g x) * character a x) *
          ∑ y : Vec, sign (h y) * character a y)) =
      ∑ a : Vec, ∑ x : Vec, ∑ y : Vec,
        character t a *
          ((sign (g x) * character a x) *
            (sign (h y) * character a y)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
    _ = ∑ x : Vec, ∑ y : Vec, ∑ a : Vec,
        character t a *
          ((sign (g x) * character a x) *
            (sign (h y) * character a y)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x : Vec, ∑ y : Vec,
        sign (g x) * sign (h y) *
          ∑ a : Vec, character a (t + x + y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have hchar :
          character t a * character a x * character a y =
            character a (t + x + y) := by
        rw [character_comm t a, character_add_right, character_add_right]
      rw [← hchar]
      ring
    _ = ∑ x : Vec, ∑ y : Vec,
        sign (g x) * sign (h y) *
          (if t + x + y = 0 then 128 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [show (∑ a : Vec, character a (t + x + y)) =
          if t + x + y = 0 then (128 : Int) else 0 by
        simpa [character_comm] using character_sum (t + x + y)]
    _ = ∑ x : Vec, 128 * (sign (g x) * sign (h (x + t))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show (∑ y : Vec, sign (g x) * sign (h y) *
          (if t + x + y = 0 then 128 else 0)) =
          128 * (sign (g x) * sign (h (x + t))) by
        have hiff (y : Vec) : t = x + y ↔ y = x + t := by
          constructor
          · intro h
            calc
              y = x + (x + y) := (LeanCipher.f2vec_cancel_left x y).symm
              _ = x + t := by rw [← h]
          · intro h
            calc
              t = x + (x + t) := (LeanCipher.f2vec_cancel_left x t).symm
              _ = x + y := by rw [h]
        simp only [add_assoc, add_eq_zero_iff_eq, hiff]
        simp
        ring]
    _ = 128 * crossCorrelation g h t := by
      simp only [crossCorrelation, sign_add]
      rw [Finset.mul_sum]

theorem hadamard_normalizedWalsh_product
    (g h : Vec -> ZMod 2) (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        (fun a => normalizedWalsh g a * normalizedWalsh h a) t =
      32 * crossCorrelation g h t := by
  have hfour :
      4 * hadamardTransform (fun a x : Vec => character a x)
          (fun a => normalizedWalsh g a * normalizedWalsh h a) t =
        hadamardTransform (fun a x : Vec => character a x)
          (fun a => walsh g a * walsh h a) t := by
    simp only [hadamardTransform, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← two_mul_normalizedWalsh g a,
      ← two_mul_normalizedWalsh h a]
    ring
  rw [hadamard_walsh_product] at hfour
  omega

theorem hadamard_normalizedWalsh_square
    (g : Vec -> ZMod 2) (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        (fun a => normalizedWalsh g a ^ 2) t =
      32 * autocorrelation g t := by
  simpa [pow_two, autocorrelation, crossCorrelation] using
    hadamard_normalizedWalsh_product g g t

/-! The product first bit and its quadratic Reed--Muller consequence. -/

private theorem eight_dvd_sq_sub_one_of_odd
    {z : Int} (hz : Odd z) : (8 : Int) ∣ z ^ 2 - 1 := by
  obtain ⟨k, hk⟩ := hz
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self k
  refine ⟨r, ?_⟩
  rw [hk]
  calc
    (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
    _ = 8 * r := by rw [hr]; ring

theorem four_dvd_normalizedWalsh_product_add_one
    (g h : Vec -> ZMod 2) (hg : Odd (weight g))
    (hsum : ∀ a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a)
    (a : Vec) :
    (4 : Int) ∣ normalizedWalsh g a * normalizedWalsh h a + 1 := by
  obtain ⟨r, hr⟩ := hsum a
  obtain ⟨s, hs⟩ := normalizedWalsh_odd_of_weight_odd g hg a
  have hq : normalizedWalsh h a =
      4 * r - normalizedWalsh g a := by omega
  refine ⟨r * normalizedWalsh g a - s * (s + 1), ?_⟩
  rw [hq, hs]
  ring

theorem four_mul_productFirstBit
    (g h : Vec -> ZMod 2) (hg : Odd (weight g))
    (hsum : ∀ a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a)
    (a : Vec) :
    4 * productFirstBit g h a =
      normalizedWalsh g a * normalizedWalsh h a + 1 := by
  obtain ⟨r, hr⟩ :=
    four_dvd_normalizedWalsh_product_add_one g h hg hsum a
  simp only [productFirstBit]
  rw [hr]
  omega

theorem hadamard_const_one (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        (fun _ => (1 : Int)) t =
      if t = 0 then 128 else 0 := by
  simpa [hadamardTransform] using character_sum t

theorem hadamard_pointMassZero (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        pointMassZero t = 1 := by
  classical
  simp [hadamardTransform, pointMassZero]

theorem hadamard_productFirstBit
    (g h : Vec -> ZMod 2) (hg : Odd (weight g))
    (hsum : ∀ a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a)
    (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        (productFirstBit g h) t =
      8 * crossCorrelation g h t + 32 * pointMassZero t := by
  have hscaled :
      4 * hadamardTransform (fun a x : Vec => character a x)
          (productFirstBit g h) t =
        hadamardTransform (fun a x : Vec => character a x)
            (fun a => normalizedWalsh g a * normalizedWalsh h a) t +
          hadamardTransform (fun a x : Vec => character a x)
            (fun _ => (1 : Int)) t := by
    simp only [hadamardTransform, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have hk := four_mul_productFirstBit g h hg hsum a
    calc
      4 * (character t a * productFirstBit g h a) =
          character t a * (4 * productFirstBit g h a) := by ring
      _ = character t a *
          (normalizedWalsh g a * normalizedWalsh h a + 1) := by rw [hk]
      _ = _ := by ring
  rw [hadamard_normalizedWalsh_product, hadamard_const_one] at hscaled
  by_cases ht : t = 0
  · subst t
    simp [pointMassZero] at hscaled ⊢
    omega
  · simp [pointMassZero, ht] at hscaled ⊢
    omega

theorem thirtyTwo_dvd_hadamard_productFirstBit
    (g h : Vec -> ZMod 2) (hg : Odd (weight g)) (hh : Odd (weight h))
    (hsum : ∀ a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a)
    (t : Vec) :
    (32 : Int) ∣ hadamardTransform
      (fun a x : Vec => character a x) (productFirstBit g h) t := by
  rw [hadamard_productFirstBit g h hg hsum t]
  obtain ⟨r, hr⟩ := four_dvd_crossCorrelation_of_odd_weights g h hg hh t
  refine ⟨r + pointMassZero t, ?_⟩
  rw [hr]
  ring

theorem productFirstBit_quadratic_and_weight_mem
    (g h : Vec -> ZMod 2) (hg : Odd (weight g)) (hh : Odd (weight h))
    (hsum : ∀ a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a) :
    ∃ Q : QuadraticCoeff, ∃ a : Vec, ∃ c : ZMod 2,
      (∀ x, intParity (productFirstBit g h) x = quadraticEval Q a c x) ∧
        weight (intParity (productFirstBit g h)) ∈ quadraticWeightSet := by
  apply hadamard_dvd32_implies_quadratic_and_weight_mem
  exact thirtyTwo_dvd_hadamard_productFirstBit g h hg hh hsum

/-! The individual-slice first bit and its quadratic Reed--Muller consequence. -/

theorem eight_mul_squareFirstBit
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) (a : Vec) :
    8 * squareFirstBit g a = normalizedWalsh g a ^ 2 - 1 := by
  obtain ⟨r, hr⟩ := eight_dvd_sq_sub_one_of_odd
    (normalizedWalsh_odd_of_weight_odd g hg a)
  simp only [squareFirstBit]
  rw [hr]
  omega

theorem hadamard_squareFirstBit
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        (squareFirstBit g) t =
      4 * autocorrelation g t - 16 * pointMassZero t := by
  have hscaled :
      8 * hadamardTransform (fun a x : Vec => character a x)
          (squareFirstBit g) t =
        hadamardTransform (fun a x : Vec => character a x)
            (fun a => normalizedWalsh g a ^ 2) t -
          hadamardTransform (fun a x : Vec => character a x)
            (fun _ => (1 : Int)) t := by
    simp only [hadamardTransform, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have hu := eight_mul_squareFirstBit g hg a
    calc
      8 * (character t a * squareFirstBit g a) =
          character t a * (8 * squareFirstBit g a) := by ring
      _ = character t a * (normalizedWalsh g a ^ 2 - 1) := by rw [hu]
      _ = _ := by ring
  rw [hadamard_normalizedWalsh_square, hadamard_const_one] at hscaled
  by_cases ht : t = 0
  · subst t
    simp [pointMassZero] at hscaled ⊢
    omega
  · simp [pointMassZero, ht] at hscaled ⊢
    omega

theorem hadamard_correctedSquareFirstBit
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) (t : Vec) :
    hadamardTransform (fun a x : Vec => character a x)
        (correctedSquareFirstBit g) t =
      4 * autocorrelation g t - 16 * pointMassZero t - 16 := by
  rw [show hadamardTransform (fun a x : Vec => character a x)
      (correctedSquareFirstBit g) t =
      hadamardTransform (fun a x : Vec => character a x)
          (squareFirstBit g) t -
        16 * hadamardTransform (fun a x : Vec => character a x)
          pointMassZero t by
    simp only [hadamardTransform, correctedSquareFirstBit]
    calc
      (∑ x : Vec, character t x *
          (squareFirstBit g x - 16 * pointMassZero x)) =
          ∑ x : Vec, (character t x * squareFirstBit g x -
            16 * (character t x * pointMassZero x)) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = (∑ x : Vec, character t x * squareFirstBit g x) -
          ∑ x : Vec, 16 * (character t x * pointMassZero x) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ x : Vec, character t x * squareFirstBit g x) -
          16 * ∑ x : Vec, character t x * pointMassZero x := by
            rw [Finset.mul_sum]]
  rw [hadamard_squareFirstBit g hg, hadamard_pointMassZero]
  norm_num

theorem thirtyTwo_dvd_hadamard_correctedSquareFirstBit
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) (t : Vec) :
    (32 : Int) ∣ hadamardTransform (fun a x : Vec => character a x)
      (correctedSquareFirstBit g) t := by
  rw [hadamard_correctedSquareFirstBit g hg t]
  by_cases ht : t = 0
  · subst t
    refine ⟨15, ?_⟩
    simp [pointMassZero]
  · obtain ⟨r, hr⟩ :=
      autocorrelation_div_four_odd_of_weight_odd g hg ht
    have hcorr : autocorrelation g t = 4 * (2 * r + 1) := by
      rw [← four_mul_autocorrelationQuarter g t, hr]
    refine ⟨r, ?_⟩
    rw [hcorr]
    simp [pointMassZero, ht]
    ring

theorem intParity_correctedSquareFirstBit
    (g : Vec -> ZMod 2) :
    intParity (correctedSquareFirstBit g) = intParity (squareFirstBit g) := by
  funext x
  have h16 : (16 : ZMod 2) = 0 := by decide
  change ((squareFirstBit g x - 16 * pointMassZero x : Int) : ZMod 2) =
    (squareFirstBit g x : ZMod 2)
  push_cast
  rw [h16]
  ring

theorem squareFirstBit_quadratic_and_weight_mem
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) :
    ∃ Q : QuadraticCoeff, ∃ a : Vec, ∃ c : ZMod 2,
      (∀ x, intParity (squareFirstBit g) x = quadraticEval Q a c x) ∧
        weight (intParity (squareFirstBit g)) ∈ quadraticWeightSet := by
  obtain ⟨Q, a, c, hrepr, hweight⟩ :=
    hadamard_dvd32_implies_quadratic_and_weight_mem
      (correctedSquareFirstBit g)
      (thirtyTwo_dvd_hadamard_correctedSquareFirstBit g hg)
  refine ⟨Q, a, c, ?_, ?_⟩
  · intro x
    rw [← intParity_correctedSquareFirstBit g]
    exact hrepr x
  · rw [← intParity_correctedSquareFirstBit g]
    exact hweight

/-! The exact fourth-moment identity and the odd-slice congruence. -/

theorem normalizedWalsh_fourth_moment_identity
    (g : Vec -> ZMod 2) :
    (∑ a : Vec, normalizedWalsh g a ^ 4) =
      128 * ∑ t : Vec, (autocorrelation g t / 4) ^ 2 := by
  have hparse := hadamard_parseval
    (fun a x : Vec => character a x)
    (fun a => normalizedWalsh g a ^ 2)
    (128 : Int) character_columns_orthogonal
  simp_rw [hadamard_normalizedWalsh_square] at hparse
  have hleft :
      (∑ t : Vec, (32 * autocorrelation g t) ^ 2) =
        16384 * ∑ t : Vec, (autocorrelation g t / 4) ^ 2 := by
    calc
      (∑ t : Vec, (32 * autocorrelation g t) ^ 2) =
          ∑ t : Vec, 16384 * (autocorrelation g t / 4) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t _
            have hquarter := four_mul_autocorrelationQuarter g t
            have hscaled : 32 * autocorrelation g t =
                128 * (autocorrelation g t / 4) := by
              calc
                32 * autocorrelation g t =
                    32 * (4 * (autocorrelation g t / 4)) :=
                      congrArg (32 * ·) hquarter.symm
                _ = 128 * (autocorrelation g t / 4) := by ring
            rw [hscaled]
            ring
      _ = 16384 * ∑ t : Vec, (autocorrelation g t / 4) ^ 2 := by
            rw [Finset.mul_sum]
  have hright :
      128 * ∑ a : Vec, (normalizedWalsh g a ^ 2) ^ 2 =
        128 * ∑ a : Vec, normalizedWalsh g a ^ 4 := by
    apply congrArg (128 * ·)
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hleft, hright] at hparse
  omega

private theorem odd_square_modeq_one_mod_eight
    {z : Int} (hz : Odd z) : z ^ 2 ≡ 1 [ZMOD 8] := by
  obtain ⟨k, hk⟩ := hz
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self k
  rw [Int.modEq_iff_dvd]
  refine ⟨-r, ?_⟩
  rw [hk]
  calc
    1 - (2 * k + 1) ^ 2 = -4 * (k * (k + 1)) := by ring
    _ = 8 * -r := by rw [hr]; ring

private theorem autocorrelation_quarter_square_sum_modeq
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) :
    (∑ t : Vec, (autocorrelation g t / 4) ^ 2) ≡ 127 [ZMOD 8] := by
  classical
  have hterm (t : Vec) :
      (autocorrelation g t / 4) ^ 2 ≡
        (if t = 0 then 0 else 1) [ZMOD 8] := by
    by_cases ht : t = 0
    · subst t
      norm_num
    · simpa [ht] using odd_square_modeq_one_mod_eight
        (autocorrelation_div_four_odd_of_weight_odd g hg ht)
  have hsum :
      (∑ t : Vec, (autocorrelation g t / 4) ^ 2) ≡
        (∑ t : Vec, if t = 0 then (0 : Int) else 1) [ZMOD 8] := by
    exact Int.ModEq.sum fun t _ => hterm t
  have hindicator :
      (∑ t : Vec, if t = 0 then (0 : Int) else 1) = 127 := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const,
      nsmul_eq_mul]
    rw [show (Finset.univ.filter fun t : Vec => t ≠ 0) =
        Finset.univ.erase 0 by
      simpa only [ne_eq] using
        Finset.filter_ne' (Finset.univ : Finset Vec) 0]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]
    norm_num [f2Vec_card]
  rw [hindicator] at hsum
  exact hsum

theorem normalizedWalsh_fourth_moment_modeq
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) :
    (∑ a : Vec, normalizedWalsh g a ^ 4) ≡ 896 [ZMOD 1024] := by
  have hsum := autocorrelation_quarter_square_sum_modeq g hg
  rw [Int.modEq_iff_dvd] at hsum ⊢
  obtain ⟨r, hr⟩ := hsum
  refine ⟨r - 15, ?_⟩
  rw [normalizedWalsh_fourth_moment_identity]
  have hs : (∑ t : Vec, (autocorrelation g t / 4) ^ 2) =
      127 - 8 * r := by omega
  rw [hs]
  ring

theorem normalizedWalsh_fourth_moment_mod
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) :
    (∑ a : Vec, normalizedWalsh g a ^ 4) % 1024 = 896 := by
  have h := normalizedWalsh_fourth_moment_modeq g hg
  change (∑ a : Vec, normalizedWalsh g a ^ 4) % 1024 =
    (896 : Int) % 1024 at h
  norm_num at h ⊢
  exact h

end LeanCipher.BalancedEightSliceArithmetic

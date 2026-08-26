import LeanCipher.BalancedEightLocal
import LeanCipher.BalancedEightQuadratic
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEightTerminal

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEight
open LeanCipher.BalancedEightCertificates
open LeanCipher.BalancedEightQuadratic
open LeanCipher.GeneratedVerifiedLemmas

abbrev Vec := V 7

def halfWalsh (g : Vec -> ZMod 2) (a : Vec) : Int :=
  64 - (weight fun x => g x + f2Dot a x : Int)

theorem two_mul_halfWalsh (g : Vec -> ZMod 2) (a : Vec) :
    2 * halfWalsh g a = walsh g a := by
  rw [walsh_eq_card_sub_two_mul_weight]
  simp only [halfWalsh]
  norm_num
  ring

/-! ## Common sign normalization for a pair of oriented slices -/

theorem supportXor_slices (F : V 8 -> ZMod 2) :
    supportXor (lowerSlice F) + supportXor (upperSlice F) =
      head (supportXor F) := by
  classical
  funext i
  change
    (∑ x : Vec, F (join x 0) * x i) +
      (∑ x : Vec, F (join x 1) * x i) =
        ∑ x : V 8, F x * x i.castSucc
  have hsplit := splitEquiv.symm.sum_comp
    (fun x : V 8 => F x * x i.castSucc)
  calc
    _ = ∑ y : V 7 × ZMod 2, F (join y.1 y.2) * y.1 i := by
      rw [Fintype.sum_prod_type]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
      simp
    _ = ∑ x : V 8, F x * x i.castSucc := by
      simpa only [splitEquiv_symm_apply, join, Fin.snoc_castSucc] using hsplit

theorem supportXor_comp_shear_head (f : V 8 -> ZMod 2) (ell : Vec) :
    head (supportXor (fun x => f (shear ell x))) = head (supportXor f) := by
  classical
  funext i
  change (∑ x : V 8, f (shear ell x) * x i.castSucc) =
    ∑ x : V 8, f x * x i.castSucc
  have hreindex := (shearEquiv ell).sum_comp
    (fun x : V 8 => f x * x i.castSucc)
  calc
    _ = ∑ x : V 8, f (shear ell x) * (shear ell x) i.castSucc := by
      apply Finset.sum_congr rfl
      intro x _
      have hx := congrFun (head_shear ell x) i
      change (shear ell x) i.castSucc = x i.castSucc at hx
      rw [hx]
    _ = _ := hreindex

theorem direction_supportXor_sum (f : V 8 -> ZMod 2) (ell : Vec) :
    supportXor (directionLowerSlice f ell) +
        supportXor (directionUpperSlice f ell) = head (supportXor f) := by
  rw [show directionLowerSlice f ell =
      lowerSlice (fun x => f (shear ell x)) by rfl,
    show directionUpperSlice f ell =
      upperSlice (fun x => f (shear ell x)) by rfl,
    supportXor_slices, supportXor_comp_shear_head]

theorem oriented_supportXor_eq
    (f : V 8 -> ZMod 2) (hnorm : supportXor f = lastBasis) (ell : Vec) :
    supportXor (orientedLowerSlice f ell) =
      supportXor (orientedUpperSlice f ell) := by
  have hsum := direction_supportXor_sum f ell
  rw [hnorm, lastBasis_eq_join] at hsum
  have hhead : head (join (0 : Vec) 1) = 0 := by simp
  rw [hhead] at hsum
  have heq : supportXor (directionLowerSlice f ell) =
      supportXor (directionUpperSlice f ell) := by
    calc
      supportXor (directionLowerSlice f ell) =
          supportXor (directionLowerSlice f ell) + 0 := by simp
      _ = supportXor (directionLowerSlice f ell) +
          (supportXor (directionUpperSlice f ell) +
            supportXor (directionUpperSlice f ell)) := by
              rw [LeanCipher.f2vec_add_self]
      _ = (supportXor (directionLowerSlice f ell) +
          supportXor (directionUpperSlice f ell)) +
            supportXor (directionUpperSlice f ell) := by rw [add_assoc]
      _ = supportXor (directionUpperSlice f ell) := by rw [hsum]; simp
  by_cases h : 0 < walsh f (join ell 1)
  · simpa [orientedLowerSlice, orientedUpperSlice, h] using
      heq
  · rw [orientedLowerSlice, orientedUpperSlice, if_neg h, if_neg h]
    exact heq.symm

def commonShift (f : V 8 -> ZMod 2) (ell : Vec) : Vec :=
  supportXor (orientedLowerSlice f ell)

def pValue (f : V 8 -> ZMod 2) (ell a : Vec) : Int :=
  character a (commonShift f ell) *
    halfWalsh (orientedLowerSlice f ell) a

def qValue (f : V 8 -> ZMod 2) (ell a : Vec) : Int :=
  character a (commonShift f ell) *
    halfWalsh (orientedUpperSlice f ell) a

@[simp] theorem pValue_zero (f : V 8 -> ZMod 2) (ell : Vec) :
    pValue f ell 0 = 64 - weight (orientedLowerSlice f ell) := by
  simp [pValue, halfWalsh, f2Dot]

@[simp] theorem qValue_zero (f : V 8 -> ZMod 2) (ell : Vec) :
    qValue f ell 0 = 64 - weight (orientedUpperSlice f ell) := by
  simp [qValue, halfWalsh, f2Dot]

private theorem support_character_sum_eq
    (g : V n -> ZMod 2) (a : V n) :
    (∑ x ∈ (Finset.univ : Finset (V n)).filter (fun x => g x ≠ 0),
      character a x) =
      (weight g : Int) - 2 * (supportIntersection g a : Int) := by
  classical
  let S := (Finset.univ : Finset (V n)).filter fun x => g x ≠ 0
  let T := S.filter fun x => f2Dot a x ≠ 0
  have hT : T.card = supportIntersection g a := by
    simp only [T, S, supportIntersection]
    congr 1
    ext x
    simp
  have hS : S.card = weight g := by rfl
  change S.sum (fun x => character a x) = _
  calc
    S.sum (fun x => character a x) =
        S.sum (fun x => (1 : Int) -
          2 * if f2Dot a x ≠ 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      rcases zmod2_eq_zero_or_one (f2Dot a x) with hx | hx <;>
        simp [character, hx]
    _ = (S.card : Int) - 2 * (T.card : Int) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hindicator :
          (∑ x ∈ S, if f2Dot a x ≠ 0 then (1 : Int) else 0) =
            (T.card : Int) := by
        simpa only [T] using
          Finset.sum_boole (R := Int) (fun x => f2Dot a x ≠ 0) S
      rw [hindicator]
      simp
    _ = _ := by rw [hS, hT]

theorem halfWalsh_nonzero_formula
    (g : Vec -> ZMod 2) (a : Vec) (ha : a ≠ 0) :
    halfWalsh g a = -(weight g : Int) +
      2 * (supportIntersection g a : Int) := by
  have htwo := two_mul_halfWalsh g a
  rw [walsh_eq_neg_two_support_character_sum_of_ne_zero g a ha,
    support_character_sum_eq] at htwo
  omega

theorem four_dvd_twisted_halfWalsh_sub_zero
    (g : Vec -> ZMod 2) (hg : Odd (weight g)) (a : Vec) :
    (4 : Int) ∣ character a (supportXor g) * halfWalsh g a -
      halfWalsh g 0 := by
  by_cases ha : a = 0
  · subst a
    simp
  · have hp := halfWalsh_nonzero_formula g a ha
    have hp0 : halfWalsh g 0 = 64 - (weight g : Int) := by
      simp [halfWalsh, f2Dot]
    have hparity := supportIntersection_cast_eq_dot g a
    rcases zmod2_eq_zero_or_one (f2Dot a (supportXor g)) with hdot | hdot
    · have hN : Even (supportIntersection g a) := by
        apply ZMod.natCast_eq_zero_iff_even.mp
        simpa [hdot] using hparity
      obtain ⟨r, hr⟩ := hN
      refine ⟨(r : Int) - 16, ?_⟩
      rw [hp, hp0, character, hdot, sign_zero, one_mul, hr]
      push_cast
      ring
    · have hN : Odd (supportIntersection g a) := by
        rw [← Nat.not_even_iff_odd]
        intro hEven
        have hzero : ((supportIntersection g a : Nat) : ZMod 2) = 0 :=
          ZMod.natCast_eq_zero_iff_even.mpr hEven
        rw [hzero, hdot] at hparity
        norm_num at hparity
      obtain ⟨r, hr⟩ := hg
      obtain ⟨s, hs⟩ := hN
      refine ⟨(r : Int) - (s : Int) - 16, ?_⟩
      rw [hp, hp0, character, hdot, sign_one, hr, hs]
      push_cast
      ring

theorem four_dvd_pValue_sub_zero
    (f : V 8 -> ZMod 2) (ell : Vec)
    (hodd : Odd (weight (orientedLowerSlice f ell))) (a : Vec) :
    (4 : Int) ∣ pValue f ell a - pValue f ell 0 := by
  simpa [pValue, commonShift] using
    four_dvd_twisted_halfWalsh_sub_zero
      (orientedLowerSlice f ell) hodd a

theorem four_dvd_qValue_sub_zero
    (f : V 8 -> ZMod 2) (hnorm : supportXor f = lastBasis) (ell : Vec)
    (hodd : Odd (weight (orientedUpperSlice f ell))) (a : Vec) :
    (4 : Int) ∣ qValue f ell a - qValue f ell 0 := by
  have hshift := oriented_supportXor_eq f hnorm ell
  unfold qValue commonShift
  rw [hshift]
  simpa only [character, f2Dot_zero_left, sign_zero, one_mul] using
    four_dvd_twisted_halfWalsh_sub_zero
      (orientedUpperSlice f ell) hodd a

theorem character_eq_one_or_neg_one (a x : V n) :
    character a x = 1 ∨ character a x = -1 := by
  rcases zmod2_eq_zero_or_one (f2Dot a x) with h | h <;>
    simp [character, h]

theorem evenMagnitude_eq_two_mul_natAbs_p_add_q
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    evenMagnitude f a = 2 * (pValue f ell a + qValue f ell a).natAbs := by
  have hsum := oriented_slice_sum f ell a
  have hp := two_mul_halfWalsh (orientedLowerSlice f ell) a
  have hq := two_mul_halfWalsh (orientedUpperSlice f ell) a
  have hscaled :
      2 * (pValue f ell a + qValue f ell a) =
        character a (commonShift f ell) * walsh f (join a 0) := by
    rw [pValue, qValue, hsum, ← hp, ← hq]
    ring
  have habs := congrArg Int.natAbs hscaled
  rcases character_eq_one_or_neg_one a (commonShift f ell) with hc | hc <;>
    simp [evenMagnitude, hc, Int.natAbs_mul] at habs ⊢ <;> omega

theorem oddMagnitude_eq_two_mul_natAbs_p_sub_q
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell a : Vec) :
    oddMagnitude f (a + ell) =
      2 * (pValue f ell a - qValue f ell a).natAbs := by
  have hne := normalized_odd_frequency_ne_zero f hf hnorm hall (a + ell)
  have hdiff := oriented_slice_difference_abs f ell a hne
  have hp := two_mul_halfWalsh (orientedLowerSlice f ell) a
  have hq := two_mul_halfWalsh (orientedUpperSlice f ell) a
  have hscaled :
      2 * (pValue f ell a - qValue f ell a) =
        character a (commonShift f ell) *
          (walsh (orientedLowerSlice f ell) a -
            walsh (orientedUpperSlice f ell) a) := by
    rw [pValue, qValue, ← hp, ← hq]
    ring
  have habs := congrArg Int.natAbs hscaled
  change
    (walsh (orientedLowerSlice f ell) a -
      walsh (orientedUpperSlice f ell) a).natAbs =
        oddMagnitude f (a + ell) at hdiff
  rcases character_eq_one_or_neg_one a (commonShift f ell) with hc | hc <;>
    simp [hc, Int.natAbs_mul, hdiff] at habs <;> omega

def categoryScore (f : V 8 -> ZMod 2) (a : Vec) : Int :=
  if oddMagnitude f a = 20 then 5
  else if oddMagnitude f a = 12 then -3
  else 1

private theorem signed_category_arithmetic_59
    {p q : Int} {even odd : Nat}
    (hp : (4 : Int) ∣ p - 5) (hq : (4 : Int) ∣ q + 5)
    (heq : even = 2 * (p + q).natAbs)
    (hoq : odd = 2 * (p - q).natAbs)
    (heven : even = 0 ∨ even = 8 ∨ even = 16)
    (hodd : odd = 4 ∨ odd = 12 ∨ odd = 20) :
    sign (if even = 8 then (1 : ZMod 2) else 0) * (p - q) =
      if odd = 20 then 10 else if odd = 12 then -6 else 2 := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  rcases heven with rfl | rfl | rfl <;>
    rcases hodd with rfl | rfl | rfl <;>
    norm_num [sign] at heq hoq ⊢ <;> omega

private theorem signed_category_arithmetic_61
    {p q : Int} {even odd : Nat}
    (hp : (4 : Int) ∣ p - 3) (hq : (4 : Int) ∣ q + 3)
    (heq : even = 2 * (p + q).natAbs)
    (hoq : odd = 2 * (p - q).natAbs)
    (heven : even = 0 ∨ even = 8 ∨ even = 16)
    (hodd : odd = 4 ∨ odd = 12 ∨ odd = 20) :
    sign (if even = 8 then (1 : ZMod 2) else 0) * (p - q) =
      if odd = 20 then -10 else if odd = 12 then 6 else -2 := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  rcases heven with rfl | rfl | rfl <;>
    rcases hodd with rfl | rfl | rfl <;>
    norm_num [sign] at heq hoq ⊢ <;> omega

theorem signed_category_identity_59
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (Rval : Vec -> ZMod 2)
    (hR : ∀ a, Rval a = if evenMagnitude f a = 8 then 1 else 0)
    (ell : Vec) (hw : weight (orientedLowerSlice f ell) = 59)
    (a : Vec) :
    sign (Rval a) * (pValue f ell a - qValue f ell a) =
      2 * categoryScore f (a + ell) := by
  have hweights := oriented_slice_weights f hf hnorm hall ell
  have hupper : weight (orientedUpperSlice f ell) = 69 := by
    rcases hweights with h | h | h <;> omega
  have hp := four_dvd_pValue_sub_zero f ell (by rw [hw]; norm_num) a
  have hq := four_dvd_qValue_sub_zero f hnorm ell
    (by rw [hupper]; norm_num) a
  rw [pValue_zero, hw] at hp
  rw [qValue_zero, hupper] at hq
  norm_num at hp hq
  rw [hR]
  have hid := signed_category_arithmetic_59 hp hq
    (evenMagnitude_eq_two_mul_natAbs_p_add_q f ell a)
    (oddMagnitude_eq_two_mul_natAbs_p_sub_q f hf hnorm hall ell a)
    (normalized_even_frequency_magnitude f hf hnorm hall a)
    (normalized_odd_frequency_magnitude f hf hnorm hall (a + ell))
  rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
      ho | ho | ho <;>
    simp [categoryScore] at hid ⊢ <;> omega

theorem signed_category_identity_61
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (Rval : Vec -> ZMod 2)
    (hR : ∀ a, Rval a = if evenMagnitude f a = 8 then 1 else 0)
    (ell : Vec) (hw : weight (orientedLowerSlice f ell) = 61)
    (a : Vec) :
    sign (Rval a) * (pValue f ell a - qValue f ell a) =
      -(2 * categoryScore f (a + ell)) := by
  have hweights := oriented_slice_weights f hf hnorm hall ell
  have hupper : weight (orientedUpperSlice f ell) = 67 := by
    rcases hweights with h | h | h <;> omega
  have hp := four_dvd_pValue_sub_zero f ell (by rw [hw]; norm_num) a
  have hq := four_dvd_qValue_sub_zero f hnorm ell
    (by rw [hupper]; norm_num) a
  rw [pValue_zero, hw] at hp
  rw [qValue_zero, hupper] at hq
  norm_num at hp hq
  rw [hR]
  have hid := signed_category_arithmetic_61 hp hq
    (evenMagnitude_eq_two_mul_natAbs_p_add_q f ell a)
    (oddMagnitude_eq_two_mul_natAbs_p_sub_q f hf hnorm hall ell a)
    (normalized_even_frequency_magnitude f hf hnorm hall a)
    (normalized_odd_frequency_magnitude f hf hnorm hall (a + ell))
  rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
      ho | ho | ho <;>
    simp [categoryScore] at hid ⊢ <;> omega

/-! ## Closed inverse-Walsh box inequality -/

theorem halfWalsh_inversion (g : Vec -> ZMod 2) (x : Vec) :
    (∑ a : Vec, halfWalsh g a * character a x) = 64 * sign (g x) := by
  have hinv := walsh_inversion g x
  have hscaled :
      2 * (∑ a : Vec, halfWalsh g a * character a x) =
        ∑ a : Vec, walsh g a * character a x := by
    calc
      _ = ∑ a : Vec, 2 * (halfWalsh g a * character a x) := by
        rw [Finset.mul_sum]
      _ = ∑ a : Vec, walsh g a * character a x := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← mul_assoc, two_mul_halfWalsh]
  rw [hinv] at hscaled
  omega

theorem pValue_inversion (f : V 8 -> ZMod 2) (ell x : Vec) :
    (∑ a : Vec, pValue f ell a * character a x) =
      64 * sign (orientedLowerSlice f ell (commonShift f ell + x)) := by
  calc
    _ = ∑ a : Vec,
        halfWalsh (orientedLowerSlice f ell) a *
          character a (commonShift f ell + x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [pValue, character_add_right]
      ring
    _ = _ := halfWalsh_inversion (orientedLowerSlice f ell)
      (commonShift f ell + x)

theorem qValue_inversion (f : V 8 -> ZMod 2) (ell x : Vec) :
    (∑ a : Vec, qValue f ell a * character a x) =
      64 * sign (orientedUpperSlice f ell (commonShift f ell + x)) := by
  calc
    _ = ∑ a : Vec,
        halfWalsh (orientedUpperSlice f ell) a *
          character a (commonShift f ell + x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [qValue, character_add_right]
      ring
    _ = _ := halfWalsh_inversion (orientedUpperSlice f ell)
      (commonShift f ell + x)

def boxTransform (T : Finset Vec) (tau : Vec -> Int) (a : Vec) : Int :=
  ∑ x ∈ T, tau x * character a x

private theorem sum_boxTransform_mul
    (T : Finset Vec) (tau u : Vec -> Int) :
    (∑ a : Vec, boxTransform T tau a * u a) =
      ∑ x ∈ T, tau x * (∑ a : Vec, u a * character a x) := by
  classical
  calc
    _ = ∑ a : Vec, ∑ x ∈ T,
        (tau x * character a x) * u a := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [boxTransform, Finset.sum_mul]
    _ = ∑ x ∈ T, ∑ a : Vec,
        (tau x * character a x) * u a := Finset.sum_comm
    _ = ∑ x ∈ T, tau x * (∑ a : Vec, u a * character a x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem box_inequality
    (f : V 8 -> ZMod 2) (ell : Vec)
    (T : Finset Vec) (tau : Vec -> Int)
    (htau : ∀ x ∈ T, tau x = 1 ∨ tau x = -1) :
    (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform T tau a * (pValue f ell a - qValue f ell a)) ≤
      128 * T.card -
        boxTransform T tau 0 * (pValue f ell 0 - qValue f ell 0) := by
  classical
  have hpoint (x : Vec) (hx : x ∈ T) :
      tau x *
        ((∑ a : Vec, pValue f ell a * character a x) -
          ∑ a : Vec, qValue f ell a * character a x) ≤ 128 := by
    rw [pValue_inversion, qValue_inversion]
    rcases htau x hx with ht | ht <;>
      rcases zmod2_eq_zero_or_one
        (orientedLowerSlice f ell (commonShift f ell + x)) with hg | hg <;>
      rcases zmod2_eq_zero_or_one
        (orientedUpperSlice f ell (commonShift f ell + x)) with hh | hh <;>
      simp [ht, hg, hh, sign]
  have hbound :
      (∑ a : Vec,
        boxTransform T tau a * (pValue f ell a - qValue f ell a)) ≤
          128 * T.card := by
    calc
      _ = (∑ a : Vec,
          boxTransform T tau a * pValue f ell a) -
          ∑ a : Vec, boxTransform T tau a * qValue f ell a := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (∑ x ∈ T, tau x *
          (∑ a : Vec, pValue f ell a * character a x)) -
          ∑ x ∈ T, tau x *
            (∑ a : Vec, qValue f ell a * character a x) := by
        rw [sum_boxTransform_mul, sum_boxTransform_mul]
      _ = ∑ x ∈ T, tau x *
          ((∑ a : Vec, pValue f ell a * character a x) -
            ∑ a : Vec, qValue f ell a * character a x) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ∑ _x ∈ T, (128 : Int) := by
        exact Finset.sum_le_sum fun x hx => hpoint x hx
      _ = 128 * T.card := by simp; ring
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset Vec))
    (f := fun a => boxTransform T tau a *
      (pValue f ell a - qValue f ell a)) (Finset.mem_univ (0 : Vec))
  have hfull :
      (∑ a : Vec,
        boxTransform T tau a * (pValue f ell a - qValue f ell a)) =
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform T tau a * (pValue f ell a - qValue f ell a)) +
      boxTransform T tau 0 * (pValue f ell 0 - qValue f ell 0) :=
    hsplit.symm
  rw [hfull] at hbound
  omega

/-! ## Global category totals and direction selection -/

def profileScore (profile : Profile) : Int :=
  5 * (profile.n20 : Int) - 3 * (profile.n12 : Int) + profile.n4

theorem magnitudeCount_eq_int_indicator_sum
    (spectrum : Vec -> Nat) (m : Nat) :
    (magnitudeCount spectrum m : Int) =
      ∑ a : Vec, if spectrum a = m then (1 : Int) else 0 := by
  simp [magnitudeCount, Finset.sum_boole]

theorem categoryScore_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) :
    (∑ a : Vec, categoryScore f a) = profileScore (spectralProfile f) := by
  have hpoint (a : Vec) :
      categoryScore f a =
        5 * (if oddMagnitude f a = 20 then (1 : Int) else 0) -
        3 * (if oddMagnitude f a = 12 then (1 : Int) else 0) +
        (if oddMagnitude f a = 4 then (1 : Int) else 0) := by
    rcases normalized_odd_frequency_magnitude f hf hnorm hall a with
        h | h | h
    · change oddMagnitude f a = 4 at h
      simp [categoryScore, h]
    · change oddMagnitude f a = 12 at h
      simp [categoryScore, h]
    · change oddMagnitude f a = 20 at h
      simp [categoryScore, h]
  calc
    _ = ∑ a : Vec,
        (5 * (if oddMagnitude f a = 20 then (1 : Int) else 0) -
        3 * (if oddMagnitude f a = 12 then (1 : Int) else 0) +
        (if oddMagnitude f a = 4 then (1 : Int) else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a
    _ = 5 * (∑ a : Vec,
          if oddMagnitude f a = 20 then (1 : Int) else 0) -
        3 * (∑ a : Vec,
          if oddMagnitude f a = 12 then (1 : Int) else 0) +
        (∑ a : Vec,
          if oddMagnitude f a = 4 then (1 : Int) else 0) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]
    _ = profileScore (spectralProfile f) := by
      rw [← magnitudeCount_eq_int_indicator_sum,
        ← magnitudeCount_eq_int_indicator_sum,
        ← magnitudeCount_eq_int_indicator_sum]
      rfl

theorem categoryScore_sum_add_right
    (f : V 8 -> ZMod 2) (ell : Vec) :
    (∑ a : Vec, categoryScore f (a + ell)) =
      ∑ a : Vec, categoryScore f a := by
  exact Fintype.sum_equiv (Equiv.addRight ell)
    (fun a : Vec => categoryScore f (a + ell))
    (categoryScore f) (fun _ => rfl)

theorem categoryScore_nonzero_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : Vec) :
    (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
      categoryScore f (a + ell)) =
        profileScore (spectralProfile f) - categoryScore f ell := by
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset Vec))
    (f := fun a => categoryScore f (a + ell))
    (Finset.mem_univ (0 : Vec))
  rw [categoryScore_sum_add_right, categoryScore_sum f hf hnorm hall] at hsplit
  simpa using (eq_sub_of_add_eq hsplit)

theorem exists_of_magnitudeCount_pos
    (spectrum : Vec -> Nat) (m : Nat)
    (hpos : 0 < magnitudeCount spectrum m) :
    ∃ a : Vec, spectrum a = m := by
  unfold magnitudeCount at hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

theorem exists_weight59_direction
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (hpos : 0 < (spectralProfile f).n20) :
    ∃ ell : Vec, oddMagnitude f ell = 20 ∧
      weight (orientedLowerSlice f ell) = 59 := by
  obtain ⟨ell, hm⟩ := exists_of_magnitudeCount_pos
    (oddMagnitude f) 20 (by simpa [spectralProfile] using hpos)
  refine ⟨ell, hm, ?_⟩
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h <;> omega

theorem exists_weight61_direction
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (hpos : 0 < (spectralProfile f).n12) :
    ∃ ell : Vec, oddMagnitude f ell = 12 ∧
      weight (orientedLowerSlice f ell) = 61 := by
  obtain ⟨ell, hm⟩ := exists_of_magnitudeCount_pos
    (oddMagnitude f) 12 (by simpa [spectralProfile] using hpos)
  refine ⟨ell, hm, ?_⟩
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h <;> omega

/-! ## The general balanced-quadratic terminal inequality -/

theorem terminal_inequality_of_weight59_certificate
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (Rval : Vec -> ZMod 2)
    (hR : ∀ a, Rval a = if evenMagnitude f a = 8 then 1 else 0)
    (ell : Vec) (hm : oddMagnitude f ell = 20)
    (hw : weight (orientedLowerSlice f ell) = 59)
    (s : Nat) (X : Finset Vec) (tau : Vec -> Int)
    (hcard : X.card = 2 ^ (2 * s))
    (htau : ∀ x ∈ X, tau x = 1 ∨ tau x = -1)
    (htauSum : (∑ x ∈ X, tau x) = -((2 ^ s : Nat) : Int))
    (htransform : ∀ a : Vec,
      (∑ x ∈ X, tau x * character a x) =
        -((2 ^ s : Nat) : Int) * sign (Rval a)) :
    profileScore (spectralProfile f) ≤ 64 * ((2 ^ s : Nat) : Int) := by
  let k : Int := ((2 ^ s : Nat) : Int)
  let tau' : Vec -> Int := fun x => -tau x
  have htau' : ∀ x ∈ X, tau' x = 1 ∨ tau' x = -1 := by
    intro x hx
    rcases htau x hx with h | h <;> simp [tau', h]
  have htheta (a : Vec) :
      boxTransform X tau' a = k * sign (Rval a) := by
    calc
      _ = -(∑ x ∈ X, tau x * character a x) := by
        simp only [boxTransform, tau', neg_mul, Finset.sum_neg_distrib]
      _ = k * sign (Rval a) := by rw [htransform]; ring
  have htheta0 : boxTransform X tau' 0 = k := by
    calc
      _ = -(∑ x ∈ X, tau x) := by
        simp [boxTransform, tau']
      _ = k := by rw [htauSum]; ring
  have hupper : weight (orientedUpperSlice f ell) = 69 := by
    rcases oriented_slice_weights f hf hnorm hall ell with h | h | h <;> omega
  have hbox :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform X tau' a * (pValue f ell a - qValue f ell a)) ≤
        128 * (((2 ^ (2 * s) : Nat) : Int)) - 10 * k := by
    calc
      _ ≤ 128 * X.card -
          boxTransform X tau' 0 * (pValue f ell 0 - qValue f ell 0) :=
        box_inequality f ell X tau' htau'
      _ = _ := by rw [hcard, htheta0, pValue_zero, qValue_zero, hw, hupper]
                  norm_num
                  ring
  have hcat := categoryScore_nonzero_sum f hf hnorm hall ell
  have hmScore : categoryScore f ell = 5 := by simp [categoryScore, hm]
  rw [hmScore] at hcat
  have hlhs :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform X tau' a * (pValue f ell a - qValue f ell a)) =
        2 * k * (profileScore (spectralProfile f) - 5) := by
    calc
      _ = ∑ a ∈ (Finset.univ : Finset Vec).erase 0,
          2 * k * categoryScore f (a + ell) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [htheta]
        have hi := signed_category_identity_59
          f hf hnorm hall Rval hR ell hw a
        calc
          k * sign (Rval a) * (pValue f ell a - qValue f ell a) =
              k * (sign (Rval a) *
                (pValue f ell a - qValue f ell a)) := by ring
          _ = k * (2 * categoryScore f (a + ell)) := by rw [hi]
          _ = _ := by ring
      _ = 2 * k *
          (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
            categoryScore f (a + ell)) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [hcat]
  rw [hlhs] at hbox
  have hk : 0 < k := by simp [k]
  have hpow : (((2 ^ (2 * s) : Nat) : Int)) = k * k := by
    simp [k, show 2 * s = s + s by omega, pow_add]
  rw [hpow] at hbox
  nlinarith

theorem terminal_inequality_of_weight61_certificate
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (Rval : Vec -> ZMod 2)
    (hR : ∀ a, Rval a = if evenMagnitude f a = 8 then 1 else 0)
    (ell : Vec) (hm : oddMagnitude f ell = 12)
    (hw : weight (orientedLowerSlice f ell) = 61)
    (s : Nat) (X : Finset Vec) (tau : Vec -> Int)
    (hcard : X.card = 2 ^ (2 * s))
    (htau : ∀ x ∈ X, tau x = 1 ∨ tau x = -1)
    (htauSum : (∑ x ∈ X, tau x) = -((2 ^ s : Nat) : Int))
    (htransform : ∀ a : Vec,
      (∑ x ∈ X, tau x * character a x) =
        -((2 ^ s : Nat) : Int) * sign (Rval a)) :
    profileScore (spectralProfile f) ≤ 64 * ((2 ^ s : Nat) : Int) := by
  let k : Int := ((2 ^ s : Nat) : Int)
  have htheta (a : Vec) :
      boxTransform X tau a = -k * sign (Rval a) := by
    simpa [boxTransform, k] using htransform a
  have htheta0 : boxTransform X tau 0 = -k := by
    simpa [boxTransform, k] using htauSum
  have hupper : weight (orientedUpperSlice f ell) = 67 := by
    rcases oriented_slice_weights f hf hnorm hall ell with h | h | h <;> omega
  have hbox :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform X tau a * (pValue f ell a - qValue f ell a)) ≤
        128 * (((2 ^ (2 * s) : Nat) : Int)) + 6 * k := by
    calc
      _ ≤ 128 * X.card -
          boxTransform X tau 0 * (pValue f ell 0 - qValue f ell 0) :=
        box_inequality f ell X tau htau
      _ = _ := by rw [hcard, htheta0, pValue_zero, qValue_zero, hw, hupper]
                  norm_num
                  ring
  have hcat := categoryScore_nonzero_sum f hf hnorm hall ell
  have hmScore : categoryScore f ell = -3 := by simp [categoryScore, hm]
  rw [hmScore] at hcat
  have hlhs :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform X tau a * (pValue f ell a - qValue f ell a)) =
        2 * k * (profileScore (spectralProfile f) + 3) := by
    calc
      _ = ∑ a ∈ (Finset.univ : Finset Vec).erase 0,
          2 * k * categoryScore f (a + ell) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [htheta]
        have hi := signed_category_identity_61
          f hf hnorm hall Rval hR ell hw a
        calc
          -k * sign (Rval a) * (pValue f ell a - qValue f ell a) =
              -k * (sign (Rval a) *
                (pValue f ell a - qValue f ell a)) := by ring
          _ = -k * (-(2 * categoryScore f (a + ell))) := by rw [hi]
          _ = _ := by ring
      _ = 2 * k *
          (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
            categoryScore f (a + ell)) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [hcat]; ring
  rw [hlhs] at hbox
  have hk : 0 < k := by simp [k]
  have hpow : (((2 ^ (2 * s) : Nat) : Int)) = k * k := by
    simp [k, show 2 * s = s + s by omega, pow_add]
  rw [hpow] at hbox
  nlinarith

/-! ## Quadratic rank and finite survivor classification -/

theorem rm2_weight_eq_profile_n8
    (f : V 8 -> ZMod 2) (R : RM2 7)
    (hR : ∀ a, rm2Eval R a =
      if evenMagnitude f a = 8 then 1 else 0) :
    weight (rm2Eval R) = (spectralProfile f).n8 := by
  classical
  change
    ((Finset.univ : Finset Vec).filter (fun a => rm2Eval R a ≠ 0)).card =
      ((Finset.univ : Finset Vec).filter
        (fun a => evenMagnitude f a = 8)).card
  congr 1
  ext a
  simp [hR a]

theorem exists_quadratic_half_rank (R : RM2 7) :
    ∃ s : Nat, s ≤ 3 ∧ polarRank R.quadratic = 2 * s := by
  obtain ⟨sFin, hs⟩ :=
    upper_triangular_reflected_rank_even_fin_q2 7 R.quadratic
  let s : Nat := sFin
  have hrank : polarRank R.quadratic = 2 * s := by
    simpa [polarRank, polarMatrix, s] using hs
  have hbound : 2 * s ≤ 7 :=
    rank_even_bound_from_reflected_rank_q2 7 s R.quadratic (by
      simpa [polarRank, polarMatrix] using hrank)
  exact ⟨s, by omega, hrank⟩

def exceptionalBalancedProfile : Profile :=
  { n20 := 112, n12 := 16, n4 := 0, n16 := 56, n8 := 64, n0 := 8 }

theorem declaredSurvivor_numeric_classification
    (profile : Profile) (hprofile : profile ∈ declaredSurvivors) :
    (profile.n8 = 56 ∧ 0 < profile.n12 ∧ 464 < profileScore profile) ∨
    (profile.n8 = 64 ∧ 0 < profile.n20 ∧
      (512 < profileScore profile ∨ profile = exceptionalBalancedProfile)) := by
  simp only [declaredSurvivors, List.mem_cons, List.not_mem_nil,
    or_false] at hprofile
  rcases hprofile with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst profile <;> norm_num [profileScore, exceptionalBalancedProfile]

/-! ## Strict rank-six certificate -/

def shiftedOddIndicator
    (f : V 8 -> ZMod 2) (ell : Vec) (m : Nat) (a : Vec) : Int :=
  if oddMagnitude f (a + ell) = m then 1 else 0

def polarKernelIndicator (R : RM2 7) (a : Vec) : Int :=
  if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then 1 else 0

theorem shiftedOddIndicator_nonzero_sum
    (f : V 8 -> ZMod 2) (ell : Vec) (m : Nat) :
    (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
      shiftedOddIndicator f ell m a) =
        (magnitudeCount (oddMagnitude f) m : Int) -
          shiftedOddIndicator f ell m 0 := by
  have htotal :
      (∑ a : Vec, shiftedOddIndicator f ell m a) =
        (magnitudeCount (oddMagnitude f) m : Int) := by
    calc
      _ = ∑ a : Vec,
          if oddMagnitude f a = m then (1 : Int) else 0 :=
        Fintype.sum_equiv (Equiv.addRight ell)
          (shiftedOddIndicator f ell m)
          (fun a => if oddMagnitude f a = m then (1 : Int) else 0)
          (fun _ => rfl)
      _ = _ := (magnitudeCount_eq_int_indicator_sum
        (oddMagnitude f) m).symm
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset Vec))
    (f := shiftedOddIndicator f ell m) (Finset.mem_univ (0 : Vec))
  rw [htotal] at hsplit
  exact eq_sub_of_add_eq hsplit

theorem polarKernelIndicator_nonzero_sum
    (R : RM2 7) (hrank : polarRank R.quadratic = 6) :
    (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
      polarKernelIndicator R a) = 1 := by
  have hcard := polarKernelSet_card_rank_six R hrank
  have htotal :
      (∑ a : Vec, polarKernelIndicator R a) = 2 := by
    calc
      _ = ((polarKernelSet R).card : Int) := by
        simpa [polarKernelIndicator, polarKernelSet] using
          (Finset.sum_boole (R := Int)
            (fun a : Vec =>
              Matrix.toLin' (polarMatrix R.quadratic) a = 0)
            Finset.univ)
      _ = 2 := by exact_mod_cast hcard
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset Vec))
    (f := polarKernelIndicator R) (Finset.mem_univ (0 : Vec))
  rw [htotal] at hsplit
  have hzero : polarKernelIndicator R 0 = 1 := by
    simp [polarKernelIndicator]
  rw [hzero] at hsplit
  omega

theorem strict_rank_six_terminal_inequality
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (R : RM2 7)
    (hR : ∀ a, rm2Eval R a =
      if evenMagnitude f a = 8 then 1 else 0)
    (hrank : polarRank R.quadratic = 6)
    (ell : Vec) (hm : oddMagnitude f ell = 12)
    (hw : weight (orientedLowerSlice f ell) = 61)
    (T : Finset Vec) (hcard : T.card = 28)
    (htransform : ∀ a : Vec, a ≠ 0 ->
      boxTransform T (fun _ => 1) a =
        if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then
          28 * sign (rm2Eval R a)
        else -4 * sign (rm2Eval R a)) :
    profileScore (spectralProfile f) ≤ 464 := by
  have hupper : weight (orientedUpperSlice f ell) = 67 := by
    rcases oriented_slice_weights f hf hnorm hall ell with h | h | h <;> omega
  have hbox :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform T (fun _ => 1) a *
          (pValue f ell a - qValue f ell a)) ≤ 3416 := by
    calc
      _ ≤ 128 * T.card -
          boxTransform T (fun _ => 1) 0 *
            (pValue f ell 0 - qValue f ell 0) :=
        box_inequality f ell T (fun _ => 1) (by simp)
      _ = 3416 := by
        rw [hcard, pValue_zero, qValue_zero, hw, hupper]
        norm_num [boxTransform]
        simp [hcard]
  have hpoint (a : Vec)
      (ha : a ∈ (Finset.univ : Finset Vec).erase 0) :
      40 * shiftedOddIndicator f ell 20 a -
          24 * shiftedOddIndicator f ell 12 a +
          8 * shiftedOddIndicator f ell 4 a -
          320 * polarKernelIndicator R a ≤
        boxTransform T (fun _ => 1) a *
          (pValue f ell a - qValue f ell a) := by
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have htheta := htransform a ha0
    have hid := signed_category_identity_61
      f hf hnorm hall (rm2Eval R) hR ell hw a
    have hmag := normalized_odd_frequency_magnitude
      f hf hnorm hall (a + ell)
    by_cases hkernel :
        Matrix.toLin' (polarMatrix R.quadratic) a = 0
    · rw [if_pos hkernel] at htheta
      have hkernelIndicator : polarKernelIndicator R a = 1 := by
        rw [polarKernelIndicator, if_pos hkernel]
      have hproduct :
          boxTransform T (fun _ => 1) a *
              (pValue f ell a - qValue f ell a) =
            -56 * categoryScore f (a + ell) := by
        rw [htheta]
        calc
          28 * sign (rm2Eval R a) *
                (pValue f ell a - qValue f ell a) =
              28 * (sign (rm2Eval R a) *
                (pValue f ell a - qValue f ell a)) := by ring
          _ = 28 * (-(2 * categoryScore f (a + ell))) := by rw [hid]
          _ = _ := by ring
      rw [hproduct, hkernelIndicator]
      rcases hmag with hmag | hmag | hmag
      · change oddMagnitude f (a + ell) = 4 at hmag
        norm_num [shiftedOddIndicator, categoryScore, hmag]
      · change oddMagnitude f (a + ell) = 12 at hmag
        norm_num [shiftedOddIndicator, categoryScore, hmag]
      · change oddMagnitude f (a + ell) = 20 at hmag
        norm_num [shiftedOddIndicator, categoryScore, hmag]
    · rw [if_neg hkernel] at htheta
      have hkernelIndicator : polarKernelIndicator R a = 0 := by
        rw [polarKernelIndicator, if_neg hkernel]
      have hproduct :
          boxTransform T (fun _ => 1) a *
              (pValue f ell a - qValue f ell a) =
            8 * categoryScore f (a + ell) := by
        rw [htheta]
        calc
          -4 * sign (rm2Eval R a) *
                (pValue f ell a - qValue f ell a) =
              -4 * (sign (rm2Eval R a) *
                (pValue f ell a - qValue f ell a)) := by ring
          _ = -4 * (-(2 * categoryScore f (a + ell))) := by rw [hid]
          _ = _ := by ring
      rw [hproduct, hkernelIndicator]
      rcases hmag with hmag | hmag | hmag
      · change oddMagnitude f (a + ell) = 4 at hmag
        norm_num [shiftedOddIndicator, categoryScore, hmag]
      · change oddMagnitude f (a + ell) = 12 at hmag
        norm_num [shiftedOddIndicator, categoryScore, hmag]
      · change oddMagnitude f (a + ell) = 20 at hmag
        norm_num [shiftedOddIndicator, categoryScore, hmag]
  have hsum :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        (40 * shiftedOddIndicator f ell 20 a -
          24 * shiftedOddIndicator f ell 12 a +
          8 * shiftedOddIndicator f ell 4 a -
          320 * polarKernelIndicator R a)) ≤
      ∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        boxTransform T (fun _ => 1) a *
          (pValue f ell a - qValue f ell a) :=
    Finset.sum_le_sum fun a ha => hpoint a ha
  have h20 :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        shiftedOddIndicator f ell 20 a) =
          ((spectralProfile f).n20 : Int) := by
    rw [shiftedOddIndicator_nonzero_sum]
    simp [shiftedOddIndicator, hm, spectralProfile]
  have h12 :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        shiftedOddIndicator f ell 12 a) =
          ((spectralProfile f).n12 : Int) - 1 := by
    rw [shiftedOddIndicator_nonzero_sum]
    simp [shiftedOddIndicator, hm, spectralProfile]
  have h4 :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        shiftedOddIndicator f ell 4 a) =
          ((spectralProfile f).n4 : Int) := by
    rw [shiftedOddIndicator_nonzero_sum]
    simp [shiftedOddIndicator, hm, spectralProfile]
  have hkernel := polarKernelIndicator_nonzero_sum R hrank
  have hlower :
      (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
        (40 * shiftedOddIndicator f ell 20 a -
          24 * shiftedOddIndicator f ell 12 a +
          8 * shiftedOddIndicator f ell 4 a -
          320 * polarKernelIndicator R a)) =
        40 * ((spectralProfile f).n20 : Int) -
          24 * (((spectralProfile f).n12 : Int) - 1) +
          8 * ((spectralProfile f).n4 : Int) - 320 := by
    calc
      _ = 40 * (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
            shiftedOddIndicator f ell 20 a) -
          24 * (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
            shiftedOddIndicator f ell 12 a) +
          8 * (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
            shiftedOddIndicator f ell 4 a) -
          320 * (∑ a ∈ (Finset.univ : Finset Vec).erase 0,
            polarKernelIndicator R a) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
      _ = _ := by rw [h20, h12, h4, hkernel]; ring
  rw [hlower] at hsum
  have hnumeric := hsum.trans hbox
  unfold profileScore
  omega

theorem strict_terminal_of_balanced_rank_six
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (R : RM2 7)
    (hR : ∀ a, rm2Eval R a =
      if evenMagnitude f a = 8 then 1 else 0)
    (hrank : polarRank R.quadratic = 6)
    (hweight : weight (rm2Eval R) = 64)
    (hpos : 0 < (spectralProfile f).n12) :
    profileScore (spectralProfile f) ≤ 464 := by
  obtain ⟨ell, hm, hw⟩ :=
    exists_weight61_direction f hf hnorm hall hpos
  obtain ⟨z, hz, hcard, hnegative⟩ :=
    balanced_rank_six_negative_walsh_certificate R hrank hweight
  apply strict_rank_six_terminal_inequality
    f hf hnorm hall R hR hrank ell hm hw (negativeWalshSet R) hcard
  intro a ha0
  specialize hnegative a
  have hboxTransform :
      boxTransform (negativeWalshSet R) (fun _ => 1) a =
        negativeWalshTransform R a := by
    simp [boxTransform, negativeWalshTransform]
  rw [hboxTransform]
  by_cases hkernel :
      Matrix.toLin' (polarMatrix R.quadratic) a = 0
  · have hRa := balanced_rank_six_polarKernel_value
      R hrank hweight a hkernel
    simp only [if_neg ha0] at hRa
    rw [if_pos hkernel, if_neg ha0] at hnegative
    rw [if_pos hkernel, hnegative, hRa]
    norm_num [sign]
  · rw [if_neg hkernel] at hnegative ⊢
    exact hnegative

theorem strict_terminal_of_weight_56
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (R : RM2 7)
    (hR : ∀ a, rm2Eval R a =
      if evenMagnitude f a = 8 then 1 else 0)
    (hrank : polarRank R.quadratic = 6)
    (hweight : weight (rm2Eval R) = 56)
    (hpos : 0 < (spectralProfile f).n12) :
    profileScore (spectralProfile f) ≤ 464 := by
  obtain ⟨ell, hm, hw⟩ :=
    exists_weight61_direction f hf hnorm hall hpos
  obtain ⟨hcard, hnegative⟩ :=
    weight_56_negative_walsh_certificate R hrank hweight
  apply strict_rank_six_terminal_inequality
    f hf hnorm hall R hR hrank ell hm hw (negativeWalshSet R) hcard
  intro a ha0
  specialize hnegative a
  have hboxTransform :
      boxTransform (negativeWalshSet R) (fun _ => 1) a =
        negativeWalshTransform R a := by
    simp [boxTransform, negativeWalshTransform]
  rw [hboxTransform]
  by_cases hkernel :
      Matrix.toLin' (polarMatrix R.quadratic) a = 0
  · have hRa := weight_56_vanishes_on_polarKernel R hweight a hkernel
    rw [if_pos hkernel] at hnegative ⊢
    rw [hnegative, hRa]
    norm_num [sign]
  · rw [if_neg hkernel] at hnegative ⊢
    exact hnegative

/-! ## Elimination of the declared finite survivor list -/

theorem declared_survivor_terminal_contradiction
    (f : V 8 -> ZMod 2)
    (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (R : RM2 7)
    (hR : ∀ a, rm2Eval R a =
      if evenMagnitude f a = 8 then 1 else 0)
    (hsurvivor : spectralProfile f ∈ declaredSurvivors) :
    False := by
  have hRweight := rm2_weight_eq_profile_n8 f R hR
  rcases declaredSurvivor_numeric_classification
      (spectralProfile f) hsurvivor with hweight56 | hbalanced
  · rcases hweight56 with ⟨hn8, hpos12, hscore⟩
    have hweight : weight (rm2Eval R) = 56 := hRweight.trans hn8
    obtain ⟨s, hs, hrank⟩ := exists_quadratic_half_rank R
    have hwalsh : walsh (rm2Eval R) (0 : Vec) = 16 := by
      rw [walsh_eq_card_sub_two_mul_weight]
      simp [hweight]
    have hwalshNe : walsh (rm2Eval R) (0 : Vec) ≠ 0 := by
      rw [hwalsh]
      norm_num
    have habs := rm2_walsh_natAbs R s hrank 0 hwalshNe
    rw [hwalsh] at habs
    have hs3 : s = 3 := by
      interval_cases s
      · norm_num at habs
      · norm_num at habs
      · norm_num at habs
      · rfl
    have hrank6 : polarRank R.quadratic = 6 := by omega
    have hstrict := strict_terminal_of_weight_56
      f hf hnorm hall R hR hrank6 hweight hpos12
    omega
  · rcases hbalanced with ⟨hn8, hpos20, hcase⟩
    have hweight : weight (rm2Eval R) = 64 := hRweight.trans hn8
    obtain ⟨s, hs, hrank⟩ := exists_quadratic_half_rank R
    obtain ⟨X, tau, hcard, hzero, htau, htauSum, htransform⟩ :=
      exists_balanced_quadratic_spectrum_certificate R s hrank hweight
    obtain ⟨ell, hm, hw⟩ :=
      exists_weight59_direction f hf hnorm hall hpos20
    have hterminal := terminal_inequality_of_weight59_certificate
      f hf hnorm hall (rm2Eval R) hR ell hm hw s X tau
        hcard htau htauSum htransform
    rcases hcase with hscore | hexceptional
    · have hbound : profileScore (spectralProfile f) ≤ 512 := by
        interval_cases s <;> norm_num at hterminal ⊢ <;> omega
      omega
    · have hscoreEq : profileScore (spectralProfile f) = 512 := by
        rw [hexceptional]
        norm_num [profileScore, exceptionalBalancedProfile]
      have hs3 : s = 3 := by
        interval_cases s
        · norm_num at hterminal
          omega
        · norm_num at hterminal
          omega
        · norm_num at hterminal
          omega
        · rfl
      have hrank6 : polarRank R.quadratic = 6 := by omega
      have hpos12 : 0 < (spectralProfile f).n12 := by
        rw [hexceptional]
        norm_num [exceptionalBalancedProfile]
      have hstrict := strict_terminal_of_balanced_rank_six
        f hf hnorm hall R hR hrank6 hweight hpos12
      omega

end LeanCipher.BalancedEightTerminal

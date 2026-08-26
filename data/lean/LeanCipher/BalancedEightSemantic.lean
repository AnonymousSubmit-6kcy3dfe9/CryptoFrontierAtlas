import LeanCipher.BalancedEightEnumerationSound
import LeanCipher.BalancedEightSliceArithmetic
import LeanCipher.BalancedEightTerminal
import LeanCipher.BalancedEightCommonQuadratic
import LeanCipher.BalancedEightSemanticScalar
import LeanCipher.BalancedEightSemanticSquare

open scoped BigOperators

namespace LeanCipher.BalancedEightSemantic

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEight
open LeanCipher.BalancedEightCertificates
open LeanCipher.BalancedEightRM
open LeanCipher.BalancedEightSliceArithmetic
open LeanCipher.BalancedEightTerminal
open LeanCipher.BalancedEightCommonQuadratic
open LeanCipher.BalancedEightSemanticScalar
open LeanCipher.BalancedEightSemanticSquare

abbrev Vec := V 7

private theorem character_eq_one_or_neg_one (a x : V n) :
    character a x = 1 ∨ character a x = -1 := by
  rcases zmod2_eq_zero_or_one (f2Dot a x) with h | h <;>
    simp [character, h]

def lowerSpectrum (f : V 8 -> ZMod 2) (ell a : Vec) : Int :=
  normalizedWalsh (orientedLowerSlice f ell) a

def upperSpectrum (f : V 8 -> ZMod 2) (ell a : Vec) : Int :=
  normalizedWalsh (orientedUpperSlice f ell) a

def twistedLowerSpectrum (f : V 8 -> ZMod 2) (ell a : Vec) : Int :=
  pValue f ell a

def twistedUpperSpectrum (f : V 8 -> ZMod 2) (ell a : Vec) : Int :=
  qValue f ell a

private theorem character_sq (a x : V n) : character a x ^ 2 = 1 := by
  rcases character_eq_one_or_neg_one a x with h | h <;> simp [h]

theorem twistedLowerSpectrum_eq
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    twistedLowerSpectrum f ell a =
      character a (commonShift f ell) * lowerSpectrum f ell a := by
  rfl

theorem twistedUpperSpectrum_eq
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    twistedUpperSpectrum f ell a =
      character a (commonShift f ell) * upperSpectrum f ell a := by
  rfl

theorem twisted_product_eq
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    twistedLowerSpectrum f ell a * twistedUpperSpectrum f ell a =
      lowerSpectrum f ell a * upperSpectrum f ell a := by
  rw [twistedLowerSpectrum_eq, twistedUpperSpectrum_eq]
  have hc := character_sq a (commonShift f ell)
  calc
    character a (commonShift f ell) * lowerSpectrum f ell a *
        (character a (commonShift f ell) * upperSpectrum f ell a) =
      character a (commonShift f ell) ^ 2 *
        (lowerSpectrum f ell a * upperSpectrum f ell a) := by ring
    _ = _ := by rw [hc]; ring

theorem twisted_lower_square_eq
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    twistedLowerSpectrum f ell a ^ 2 = lowerSpectrum f ell a ^ 2 := by
  rw [twistedLowerSpectrum_eq, mul_pow, character_sq]
  simp

theorem twisted_upper_square_eq
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    twistedUpperSpectrum f ell a ^ 2 = upperSpectrum f ell a ^ 2 := by
  rw [twistedUpperSpectrum_eq, mul_pow, character_sq]
  simp

theorem evenMagnitude_eq_normalized_sum
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    evenMagnitude f a =
      2 * (lowerSpectrum f ell a + upperSpectrum f ell a).natAbs := by
  have hsum := oriented_slice_sum f ell a
  have hl := two_mul_normalizedWalsh (orientedLowerSlice f ell) a
  have hu := two_mul_normalizedWalsh (orientedUpperSlice f ell) a
  unfold evenMagnitude lowerSpectrum upperSpectrum
  rw [hsum, <- hl, <- hu]
  rw [show 2 * normalizedWalsh (orientedLowerSlice f ell) a +
      2 * normalizedWalsh (orientedUpperSlice f ell) a =
      2 * (normalizedWalsh (orientedLowerSlice f ell) a +
        normalizedWalsh (orientedUpperSlice f ell) a) by ring]
  simp [Int.natAbs_mul]

theorem oddMagnitude_eq_normalized_difference
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell a : Vec) :
    oddMagnitude f (a + ell) =
      2 * (lowerSpectrum f ell a - upperSpectrum f ell a).natAbs := by
  have hne := normalized_odd_frequency_ne_zero f hf hnorm hall (a + ell)
  have hdiff := oriented_slice_difference_abs f ell a hne
  have hl := two_mul_normalizedWalsh (orientedLowerSlice f ell) a
  have hu := two_mul_normalizedWalsh (orientedUpperSlice f ell) a
  unfold lowerSpectrum upperSpectrum
  rw [<- hl, <- hu] at hdiff
  rw [show 2 * normalizedWalsh (orientedLowerSlice f ell) a -
      2 * normalizedWalsh (orientedUpperSlice f ell) a =
      2 * (normalizedWalsh (orientedLowerSlice f ell) a -
        normalizedWalsh (orientedUpperSlice f ell) a) by ring] at hdiff
  simp only [Int.natAbs_mul] at hdiff
  norm_num at hdiff
  exact hdiff.symm

private theorem normalized_spectrum_natAbs_le_nine
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell a : Vec) :
    (lowerSpectrum f ell a).natAbs <= 9 /\
      (upperSpectrum f ell a).natAbs <= 9 := by
  let p := lowerSpectrum f ell a
  let q := upperSpectrum f ell a
  have heq := evenMagnitude_eq_normalized_sum f ell a
  have hoq := oddMagnitude_eq_normalized_difference f hf hnorm hall ell a
  have heven := normalized_even_frequency_magnitude f hf hnorm hall a
  have hodd := normalized_odd_frequency_magnitude f hf hnorm hall (a + ell)
  have hr : (p + q).natAbs <= 8 := by
    change (lowerSpectrum f ell a + upperSpectrum f ell a).natAbs <= 8
    rcases heven with h | h | h <;>
      change evenMagnitude f a = _ at h <;> omega
  have hs : (p - q).natAbs <= 10 := by
    change (lowerSpectrum f ell a - upperSpectrum f ell a).natAbs <= 10
    rcases hodd with h | h | h <;>
      change oddMagnitude f (a + ell) = _ at h <;> omega
  have hpTriangle := Int.natAbs_add_le (p + q) (p - q)
  have hqTriangle := Int.natAbs_add_le (p + q) (q - p)
  have hneg : (q - p).natAbs = (p - q).natAbs := by
    rw [show q - p = -(p - q) by ring, Int.natAbs_neg]
  have hpDouble : (p + q) + (p - q) = 2 * p := by ring
  have hqDouble : (p + q) + (q - p) = 2 * q := by ring
  rw [hpDouble, Int.natAbs_mul] at hpTriangle
  rw [hqDouble, Int.natAbs_mul, hneg] at hqTriangle
  norm_num at hpTriangle hqTriangle
  constructor <;> omega

private theorem twisted_spectrum_natAbs_le_nine
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell a : Vec) :
    (twistedLowerSpectrum f ell a).natAbs <= 9 /\
      (twistedUpperSpectrum f ell a).natAbs <= 9 := by
  obtain ⟨hl, hu⟩ := normalized_spectrum_natAbs_le_nine
    f hf hnorm hall ell a
  rw [twistedLowerSpectrum_eq, twistedUpperSpectrum_eq,
    Int.natAbs_mul, Int.natAbs_mul]
  rcases character_eq_one_or_neg_one a (commonShift f ell) with
      hc | hc <;> simp [hc, hl, hu]

private theorem twistedLowerSpectrum_sum_natAbs
    (f : V 8 -> ZMod 2) (ell : Vec) :
    (∑ a : Vec, twistedLowerSpectrum f ell a).natAbs = 64 := by
  change (∑ a : Vec, pValue f ell a).natAbs = 64
  have hinv := pValue_inversion f ell 0
  simp only [character, f2Dot_zero_right,
    sign_zero, mul_one, add_zero] at hinv
  rw [hinv]
  rcases zmod2_eq_zero_or_one
      (orientedLowerSlice f ell (commonShift f ell)) with h | h <;>
    simp [h]

private theorem twistedUpperSpectrum_sum_natAbs
    (f : V 8 -> ZMod 2) (ell : Vec) :
    (∑ a : Vec, twistedUpperSpectrum f ell a).natAbs = 64 := by
  change (∑ a : Vec, qValue f ell a).natAbs = 64
  have hinv := qValue_inversion f ell 0
  simp only [character, f2Dot_zero_right,
    sign_zero, mul_one, add_zero] at hinv
  rw [hinv]
  rcases zmod2_eq_zero_or_one
      (orientedUpperSlice f ell (commonShift f ell)) with h | h <;>
    simp [h]

def absNineCount (gamma : Vec -> Int) : Nat :=
  ((Finset.univ : Finset Vec).filter fun a => (gamma a).natAbs = 9).card

private theorem neg_natAbs_le (z : Int) : -(z.natAbs : Int) <= z := by
  have h : -z <= ((-z).natAbs : Int) := Int.le_natAbs
  rw [Int.natAbs_neg] at h
  omega

private theorem absNineCount_le_38_of_residue_one
    (gamma : Vec -> Int)
    (hres : forall a, (4 : Int) ∣ gamma a - 1)
    (hbound : forall a, (gamma a).natAbs <= 9)
    (hparseval : (∑ a : Vec, gamma a ^ 2) = 4096)
    (hsum : (∑ a : Vec, gamma a).natAbs = 64) :
    absNineCount gamma <= 38 := by
  have hpoint (a : Vec) :
      192 * (if (gamma a).natAbs = 9 then (1 : Int) else 0) <=
        gamma a ^ 2 + 10 * gamma a + 21 := by
    obtain ⟨k, hk⟩ := hres a
    have hlo := neg_natAbs_le (gamma a)
    have hhi : gamma a <= ((gamma a).natAbs : Int) := Int.le_natAbs
    have hb := hbound a
    have hklo : -2 <= k := by omega
    have hkhi : k <= 2 := by omega
    have hz : gamma a = 4 * k + 1 := by omega
    rw [hz]
    interval_cases k <;> norm_num
  have hsumPoint := Finset.sum_le_sum fun a (_ha : a ∈ (Finset.univ : Finset Vec)) =>
    hpoint a
  have hcount :
      (∑ a : Vec, if (gamma a).natAbs = 9 then (1 : Int) else 0) =
        (absNineCount gamma : Int) := by
    simp [absNineCount, Finset.sum_boole]
  have hsumUpper : (∑ a : Vec, gamma a) <= 64 := by
    have h : (∑ a : Vec, gamma a) <=
        ((∑ a : Vec, gamma a).natAbs : Int) := Int.le_natAbs
    omega
  have hleft :
      (∑ a : Vec, 192 * if (gamma a).natAbs = 9 then (1 : Int) else 0) =
        192 * (absNineCount gamma : Int) := by
    rw [← Finset.mul_sum, hcount]
  have hlinear : (∑ a : Vec, 10 * gamma a) =
      10 * ∑ a : Vec, gamma a := by rw [Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsumPoint
  rw [hleft, hparseval, hlinear, f2Vec_card] at hsumPoint
  norm_num at hsumPoint
  omega

private theorem absNineCount_le_38_of_residue_neg_one
    (gamma : Vec -> Int)
    (hres : forall a, (4 : Int) ∣ gamma a + 1)
    (hbound : forall a, (gamma a).natAbs <= 9)
    (hparseval : (∑ a : Vec, gamma a ^ 2) = 4096)
    (hsum : (∑ a : Vec, gamma a).natAbs = 64) :
    absNineCount gamma <= 38 := by
  have hpoint (a : Vec) :
      192 * (if (gamma a).natAbs = 9 then (1 : Int) else 0) <=
        gamma a ^ 2 - 10 * gamma a + 21 := by
    obtain ⟨k, hk⟩ := hres a
    have hlo := neg_natAbs_le (gamma a)
    have hhi : gamma a <= ((gamma a).natAbs : Int) := Int.le_natAbs
    have hb := hbound a
    have hklo : -2 <= k := by omega
    have hkhi : k <= 2 := by omega
    have hz : gamma a = 4 * k - 1 := by omega
    rw [hz]
    interval_cases k <;> norm_num
  have hsumPoint := Finset.sum_le_sum fun a (_ha : a ∈ (Finset.univ : Finset Vec)) =>
    hpoint a
  have hcount :
      (∑ a : Vec, if (gamma a).natAbs = 9 then (1 : Int) else 0) =
        (absNineCount gamma : Int) := by
    simp [absNineCount, Finset.sum_boole]
  have hsumLower : -(64 : Int) <= (∑ a : Vec, gamma a) := by
    have h := neg_natAbs_le (∑ a : Vec, gamma a)
    omega
  have hleft :
      (∑ a : Vec, 192 * if (gamma a).natAbs = 9 then (1 : Int) else 0) =
        192 * (absNineCount gamma : Int) := by
    rw [← Finset.mul_sum, hcount]
  have hlinear : (∑ a : Vec, 10 * gamma a) =
      10 * ∑ a : Vec, gamma a := by rw [Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumPoint
  rw [hleft, hparseval, hlinear, f2Vec_card] at hsumPoint
  norm_num at hsumPoint
  omega

private theorem absNineCount_lower_le
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) : absNineCount (twistedLowerSpectrum f ell) <= 38 := by
  have hweights := oriented_slice_weights f hf hnorm hall ell
  have hbound := fun a => (twisted_spectrum_natAbs_le_nine
    f hf hnorm hall ell a).1
  have hparseval :
      (∑ a : Vec, twistedLowerSpectrum f ell a ^ 2) = 4096 := by
    calc
      _ = ∑ a : Vec, lowerSpectrum f ell a ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        exact twisted_lower_square_eq f ell a
      _ = 4096 := normalizedWalsh_parseval (orientedLowerSlice f ell)
  rcases hweights with h59 | h61 | h63
  · apply absNineCount_le_38_of_residue_one _ _ hbound hparseval
      (twistedLowerSpectrum_sum_natAbs f ell)
    intro a
    have h := four_dvd_pValue_sub_zero f ell
      (by rw [h59.2.1]; norm_num) a
    rw [pValue_zero, h59.2.1] at h
    change (4 : Int) ∣ pValue f ell a - 1
    obtain ⟨k, hk⟩ := h
    refine ⟨k + 1, by omega⟩
  · apply absNineCount_le_38_of_residue_neg_one _ _ hbound hparseval
      (twistedLowerSpectrum_sum_natAbs f ell)
    intro a
    have h := four_dvd_pValue_sub_zero f ell
      (by rw [h61.2.1]; norm_num) a
    rw [pValue_zero, h61.2.1] at h
    change (4 : Int) ∣ pValue f ell a + 1
    obtain ⟨k, hk⟩ := h
    refine ⟨k + 1, by omega⟩
  · apply absNineCount_le_38_of_residue_one _ _ hbound hparseval
      (twistedLowerSpectrum_sum_natAbs f ell)
    intro a
    have h := four_dvd_pValue_sub_zero f ell
      (by rw [h63.2.1]; norm_num) a
    rw [pValue_zero, h63.2.1] at h
    change (4 : Int) ∣ pValue f ell a - 1
    simpa using h

private theorem absNineCount_upper_le
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) : absNineCount (twistedUpperSpectrum f ell) <= 38 := by
  have hweights := oriented_slice_weights f hf hnorm hall ell
  have hbound := fun a => (twisted_spectrum_natAbs_le_nine
    f hf hnorm hall ell a).2
  have hparseval :
      (∑ a : Vec, twistedUpperSpectrum f ell a ^ 2) = 4096 := by
    calc
      _ = ∑ a : Vec, upperSpectrum f ell a ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        exact twisted_upper_square_eq f ell a
      _ = 4096 := normalizedWalsh_parseval (orientedUpperSlice f ell)
  rcases hweights with h59 | h61 | h63
  · apply absNineCount_le_38_of_residue_neg_one _ _ hbound hparseval
      (twistedUpperSpectrum_sum_natAbs f ell)
    intro a
    have h := four_dvd_qValue_sub_zero f hnorm ell
      (by rw [h59.2.2]; norm_num) a
    rw [qValue_zero, h59.2.2] at h
    change (4 : Int) ∣ qValue f ell a + 1
    obtain ⟨k, hk⟩ := h
    refine ⟨k - 1, by omega⟩
  · apply absNineCount_le_38_of_residue_one _ _ hbound hparseval
      (twistedUpperSpectrum_sum_natAbs f ell)
    intro a
    have h := four_dvd_qValue_sub_zero f hnorm ell
      (by rw [h61.2.2]; norm_num) a
    rw [qValue_zero, h61.2.2] at h
    change (4 : Int) ∣ qValue f ell a - 1
    obtain ⟨k, hk⟩ := h
    refine ⟨k - 1, by omega⟩
  · apply absNineCount_le_38_of_residue_neg_one _ _ hbound hparseval
      (twistedUpperSpectrum_sum_natAbs f ell)
    intro a
    have h := four_dvd_qValue_sub_zero f hnorm ell
      (by rw [h63.2.2]; norm_num) a
    rw [qValue_zero, h63.2.2] at h
    change (4 : Int) ∣ qValue f ell a + 1
    simpa using h

/-! ## Oriented local-pair accounting -/

private def pairIndicator (p q : Int) (r s : Nat) : Int :=
  if p.natAbs = r ∧ q.natAbs = s then 1 else 0

private def pairSign (p q : Int) (r s : Nat) : Int :=
  pairIndicator p q r s - pairIndicator p q s r

private def pairMass (p q : Int) (r s : Nat) : Int :=
  pairIndicator p q r s + pairIndicator p q s r

private def pairCount (P Q : Vec -> Int) (r s : Nat) : Nat :=
  ((Finset.univ : Finset Vec).filter fun a =>
    (P a).natAbs = r ∧ (Q a).natAbs = s).card

private def pairDelta (P Q : Vec -> Int) (r s : Nat) : Int :=
  ∑ a : Vec, pairSign (P a) (Q a) r s

private theorem pairIndicator_sum_eq_pairCount
    (P Q : Vec -> Int) (r s : Nat) :
    (∑ a : Vec, pairIndicator (P a) (Q a) r s) =
      (pairCount P Q r s : Int) := by
  simp [pairIndicator, pairCount, Finset.sum_boole]

private theorem pairDelta_eq_count_sub
    (P Q : Vec -> Int) (r s : Nat) :
    pairDelta P Q r s =
      (pairCount P Q r s : Int) - (pairCount P Q s r : Int) := by
  unfold pairDelta pairSign
  rw [Finset.sum_sub_distrib, pairIndicator_sum_eq_pairCount,
    pairIndicator_sum_eq_pairCount]

private theorem pairMass_sum_eq_count_add
    (P Q : Vec -> Int) (r s : Nat) :
    (∑ a : Vec, pairMass (P a) (Q a) r s) =
      (pairCount P Q r s : Int) + (pairCount P Q s r : Int) := by
  unfold pairMass
  rw [Finset.sum_add_distrib, pairIndicator_sum_eq_pairCount,
    pairIndicator_sum_eq_pairCount]

private theorem delta_of_sum (m n : Nat) :
    (m : Int) - n ∈ deltas (m + n) := by
  simp only [deltas, List.mem_map]
  refine ⟨m, by simp, ?_⟩
  push_cast
  omega

private def cellIndicator (odd even oddValue evenValue : Nat) : Int :=
  if odd = oddValue ∧ even = evenValue then 1 else 0

private def absBit (z : Int) : Int :=
  if z.natAbs = 3 ∨ z.natAbs = 5 then 1 else 0

private def energyPoint (p q : Int) : Int :=
  80 * pairSign p q 9 1 + 40 * pairSign p q 7 3 +
    48 * pairSign p q 7 1 + 16 * pairSign p q 5 3 +
    24 * pairSign p q 5 1 + 8 * pairSign p q 3 1

private def fourthPoint (p q : Int) : Int :=
  6560 * pairSign p q 9 1 + 2320 * pairSign p q 7 3 +
    2400 * pairSign p q 7 1 + 544 * pairSign p q 5 3 +
    624 * pairSign p q 5 1 + 80 * pairSign p q 3 1

private def orientationPoint (p q : Int) : Int :=
  8 * pairSign p q 9 1 - 4 * pairSign p q 7 3 -
    8 * pairSign p q 7 1 + 8 * pairSign p q 5 3 +
    4 * pairSign p q 5 1 - 4 * pairSign p q 3 1

private def tableScorePoint (odd even : Nat) : Int :=
  10 * cellIndicator odd even 20 16 - 10 * cellIndicator odd even 20 8 -
    6 * cellIndicator odd even 12 16 + 10 * cellIndicator odd even 20 0 +
    2 * cellIndicator odd even 4 16 + 6 * cellIndicator odd even 12 8 -
    6 * cellIndicator odd even 12 0 - 2 * cellIndicator odd even 4 8 +
    2 * cellIndicator odd even 4 0

private def quadraticTotalPoint (odd even : Nat) : Int :=
  cellIndicator odd even 20 8 + 2 * cellIndicator odd even 20 0 +
    2 * cellIndicator odd even 4 16 + cellIndicator odd even 12 8 +
    2 * cellIndicator odd even 12 0 + cellIndicator odd even 4 8

private def quadraticDifferencePoint (p q : Int) : Int :=
  -pairSign p q 7 3 + pairSign p q 5 1 + pairSign p q 3 1

private structure OrientationPointFacts
    (p q : Int) (odd even : Nat) (eta : Int) : Prop where
  massA : pairMass p q 9 1 = cellIndicator odd even 20 16
  massB : pairMass p q 7 3 = cellIndicator odd even 20 8
  massC : pairMass p q 7 1 = cellIndicator odd even 12 16
  massE : pairMass p q 5 3 = cellIndicator odd even 4 16
  massF : pairMass p q 5 1 = cellIndicator odd even 12 8
  massH : pairMass p q 3 1 = cellIndicator odd even 4 8
  energy : p ^ 2 - q ^ 2 = energyPoint p q
  fourth : p ^ 4 - q ^ 4 = fourthPoint p q
  totalScore : p - q = eta * tableScorePoint odd even
  orientationScore : p + q = eta * orientationPoint p q
  lowerQuadratic :
    2 * absBit p = quadraticTotalPoint odd even + quadraticDifferencePoint p q
  upperQuadratic :
    2 * absBit q = quadraticTotalPoint odd even - quadraticDifferencePoint p q

private theorem orientation_point_facts
    {p q : Int} {even odd : Nat} {eta : Int}
    (heq : even = 2 * (p + q).natAbs)
    (hoq : odd = 2 * (p - q).natAbs)
    (heven : even = 0 ∨ even = 8 ∨ even = 16)
    (hodd : odd = 4 ∨ odd = 12 ∨ odd = 20)
    (hp : (4 : Int) ∣ p - eta) (hq : (4 : Int) ∣ q + eta)
    (heta : eta = 1 ∨ eta = -1)
    (hpBound : p.natAbs ≤ 9) (hqBound : q.natAbs ≤ 9) :
    OrientationPointFacts p q odd even eta := by
  subst even
  subst odd
  have hpLo := neg_natAbs_le p
  have hpHi : p ≤ (p.natAbs : Int) := Int.le_natAbs
  have hqLo := neg_natAbs_le q
  have hqHi : q ≤ (q.natAbs : Int) := Int.le_natAbs
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  rcases heta with rfl | rfl
  · have huLower : -(2 : Int) ≤ u := by omega
    have huUpper : u ≤ 2 := by omega
    have hvLower : -(2 : Int) ≤ v := by omega
    have hvUpper : v ≤ 2 := by omega
    have hpForm : p = 4 * u + 1 := by omega
    have hqForm : q = 4 * v - 1 := by omega
    interval_cases u <;> interval_cases v <;>
      norm_num at hpForm hqForm <;> subst p <;> subst q <;>
      norm_num [OrientationPointFacts, pairMass, pairSign, pairIndicator,
        cellIndicator, absBit, energyPoint, fourthPoint, orientationPoint,
        tableScorePoint, quadraticTotalPoint, quadraticDifferencePoint] at * <;>
      constructor <;>
        norm_num [pairMass, pairSign, pairIndicator, cellIndicator, absBit,
          energyPoint, fourthPoint, orientationPoint, tableScorePoint,
          quadraticTotalPoint, quadraticDifferencePoint]
  · have huLower : -(2 : Int) ≤ u := by omega
    have huUpper : u ≤ 2 := by omega
    have hvLower : -(2 : Int) ≤ v := by omega
    have hvUpper : v ≤ 2 := by omega
    have hpForm : p = 4 * u - 1 := by omega
    have hqForm : q = 4 * v + 1 := by omega
    interval_cases u <;> interval_cases v <;>
      norm_num at hpForm hqForm <;> subst p <;> subst q <;>
      norm_num [OrientationPointFacts, pairMass, pairSign, pairIndicator,
        cellIndicator, absBit, energyPoint, fourthPoint, orientationPoint,
        tableScorePoint, quadraticTotalPoint, quadraticDifferencePoint] at * <;>
      constructor <;>
        norm_num [pairMass, pairSign, pairIndicator, cellIndicator, absBit,
          energyPoint, fourthPoint, orientationPoint, tableScorePoint,
          quadraticTotalPoint, quadraticDifferencePoint]

private theorem exists_orientation_residue
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    ∃ eta : Int, (eta = 1 ∨ eta = -1) ∧
      (∀ a, (4 : Int) ∣ twistedLowerSpectrum f ell a - eta) ∧
      (∀ a, (4 : Int) ∣ twistedUpperSpectrum f ell a + eta) := by
  rcases oriented_slice_weights f hf hnorm hall ell with h59 | h61 | h63
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · intro a
      have h : (4 : Int) ∣
          twistedLowerSpectrum f ell a - twistedLowerSpectrum f ell 0 := by
        simpa only [twistedLowerSpectrum] using
          four_dvd_pValue_sub_zero f ell
            (by rw [h59.2.1]; norm_num) a
      have hzero : twistedLowerSpectrum f ell 0 = 5 := by
        simp only [twistedLowerSpectrum, pValue_zero, h59.2.1]
        norm_num
      rw [hzero] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k + 1, by omega⟩
    · intro a
      have h : (4 : Int) ∣
          twistedUpperSpectrum f ell a - twistedUpperSpectrum f ell 0 := by
        simpa only [twistedUpperSpectrum] using
          four_dvd_qValue_sub_zero f hnorm ell
            (by rw [h59.2.2]; norm_num) a
      have hzero : twistedUpperSpectrum f ell 0 = -5 := by
        simp only [twistedUpperSpectrum, qValue_zero, h59.2.2]
        norm_num
      rw [hzero] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k - 1, by omega⟩
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · intro a
      have h : (4 : Int) ∣
          twistedLowerSpectrum f ell a - twistedLowerSpectrum f ell 0 := by
        simpa only [twistedLowerSpectrum] using
          four_dvd_pValue_sub_zero f ell
            (by rw [h61.2.1]; norm_num) a
      have hzero : twistedLowerSpectrum f ell 0 = 3 := by
        simp only [twistedLowerSpectrum, pValue_zero, h61.2.1]
        norm_num
      rw [hzero] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k + 1, by omega⟩
    · intro a
      have h : (4 : Int) ∣
          twistedUpperSpectrum f ell a - twistedUpperSpectrum f ell 0 := by
        simpa only [twistedUpperSpectrum] using
          four_dvd_qValue_sub_zero f hnorm ell
            (by rw [h61.2.2]; norm_num) a
      have hzero : twistedUpperSpectrum f ell 0 = -3 := by
        simp only [twistedUpperSpectrum, qValue_zero, h61.2.2]
        norm_num
      rw [hzero] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k - 1, by omega⟩
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · intro a
      simpa only [twistedLowerSpectrum, pValue_zero, h63.2.1] using
        four_dvd_pValue_sub_zero f ell
          (by rw [h63.2.1]; norm_num) a
    · intro a
      simpa only [twistedUpperSpectrum, qValue_zero, h63.2.2] using
        four_dvd_qValue_sub_zero f hnorm ell
          (by rw [h63.2.2]; norm_num) a

private theorem local_orientation_point_facts
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) (eta : Int) (heta : eta = 1 ∨ eta = -1)
    (hp : ∀ a, (4 : Int) ∣ twistedLowerSpectrum f ell a - eta)
    (hq : ∀ a, (4 : Int) ∣ twistedUpperSpectrum f ell a + eta)
    (a : Vec) :
    OrientationPointFacts
      (twistedLowerSpectrum f ell a) (twistedUpperSpectrum f ell a)
      (oddMagnitude f (a + ell)) (evenMagnitude f a) eta := by
  apply orientation_point_facts
  · exact evenMagnitude_eq_two_mul_natAbs_p_add_q f ell a
  · exact oddMagnitude_eq_two_mul_natAbs_p_sub_q f hf hnorm hall ell a
  · exact normalized_even_frequency_magnitude f hf hnorm hall a
  · exact normalized_odd_frequency_magnitude f hf hnorm hall (a + ell)
  · exact hp a
  · exact hq a
  · exact heta
  · exact (twisted_spectrum_natAbs_le_nine f hf hnorm hall ell a).1
  · exact (twisted_spectrum_natAbs_le_nine f hf hnorm hall ell a).2

private theorem cellIndicator_sum_eq_localCellCount
    (f : V 8 -> ZMod 2) (ell : Vec) (odd even : Nat) :
    (∑ a : Vec, cellIndicator
      (oddMagnitude f (a + ell)) (evenMagnitude f a) odd even) =
      (localCellCount f ell odd even : Int) := by
  symm
  simpa [cellIndicator] using
    localCellCount_cast_eq_sum_indicator f ell odd even

private theorem pairCount_add_eq_localCellCount
    (f : V 8 -> ZMod 2) (ell : Vec) (P Q : Vec -> Int)
    (r s odd even : Nat)
    (hpoint : ∀ a, pairMass (P a) (Q a) r s =
      cellIndicator (oddMagnitude f (a + ell)) (evenMagnitude f a) odd even) :
    pairCount P Q r s + pairCount P Q s r =
      localCellCount f ell odd even := by
  have hcast :
      ((pairCount P Q r s : Nat) : Int) + (pairCount P Q s r : Int) =
        (localCellCount f ell odd even : Int) := by
    calc
      _ = ∑ a : Vec, pairMass (P a) (Q a) r s :=
        (pairMass_sum_eq_count_add P Q r s).symm
      _ = ∑ a : Vec, cellIndicator
          (oddMagnitude f (a + ell)) (evenMagnitude f a) odd even := by
        apply Finset.sum_congr rfl
        intro a _
        exact hpoint a
      _ = _ := cellIndicator_sum_eq_localCellCount f ell odd even
  exact_mod_cast hcast

private theorem pairDelta_mem_deltas
    (P Q : Vec -> Int) (r s n : Nat)
    (hsplit : pairCount P Q r s + pairCount P Q s r = n) :
    pairDelta P Q r s ∈ deltas n := by
  rw [pairDelta_eq_count_sub]
  have h := delta_of_sum (pairCount P Q r s) (pairCount P Q s r)
  rw [hsplit] at h
  exact h

private theorem orientationEnergy_pairDelta_eq_sum
    (P Q : Vec -> Int) :
    orientationEnergy
        (pairDelta P Q 9 1) (pairDelta P Q 7 3)
        (pairDelta P Q 7 1) (pairDelta P Q 5 3)
        (pairDelta P Q 5 1) (pairDelta P Q 3 1) =
      ∑ a : Vec, energyPoint (P a) (Q a) := by
  simp only [orientationEnergy, pairDelta, energyPoint, Finset.mul_sum,
    ← Finset.sum_add_distrib]

private theorem orientationFourth_pairDelta_eq_sum
    (P Q : Vec -> Int) :
    orientationFourth
        (pairDelta P Q 9 1) (pairDelta P Q 7 3)
        (pairDelta P Q 7 1) (pairDelta P Q 5 3)
        (pairDelta P Q 5 1) (pairDelta P Q 3 1) =
      ∑ a : Vec, fourthPoint (P a) (Q a) := by
  simp only [orientationFourth, pairDelta, fourthPoint, Finset.mul_sum,
    ← Finset.sum_add_distrib]

private theorem orientationScore_pairDelta_eq_sum
    (P Q : Vec -> Int) :
    orientationScore
        (pairDelta P Q 9 1) (pairDelta P Q 7 3)
        (pairDelta P Q 7 1) (pairDelta P Q 5 3)
        (pairDelta P Q 5 1) (pairDelta P Q 3 1) =
      ∑ a : Vec, orientationPoint (P a) (Q a) := by
  simp only [orientationScore, pairDelta, orientationPoint, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

private theorem orientationQuadraticDifference_pairDelta_eq_sum
    (P Q : Vec -> Int) :
    orientationQuadraticDifference
        (pairDelta P Q 7 3) (pairDelta P Q 5 1) (pairDelta P Q 3 1) =
      ∑ a : Vec, quadraticDifferencePoint (P a) (Q a) := by
  simp only [orientationQuadraticDifference, pairDelta,
    quadraticDifferencePoint, Finset.sum_add_distrib, Finset.sum_neg_distrib]

private theorem totalScore_eq_sum_tableScorePoint
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    totalScore (localTable f ell) =
      ∑ a : Vec, tableScorePoint
        (oddMagnitude f (a + ell)) (evenMagnitude f a) := by
  have htable := weightedLocalTable_eq_sum f hf hnorm hall ell
    10 (-10) (-6) 10 2 6 (-6) (-2) 2
  calc
    totalScore (localTable f ell) =
        weightedTableValue 10 (-10) (-6) 10 2 6 (-6) (-2) 2
          (localTable f ell) := by
      norm_num [totalScore, weightedTableValue]
      ring
    _ = ∑ a : Vec,
        localCellWeight 10 (-10) (-6) 10 2 6 (-6) (-2) 2
          (oddMagnitude f (a + ell)) (evenMagnitude f a) := htable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
          ho | ho | ho <;>
        rcases normalized_even_frequency_magnitude f hf hnorm hall a with
          he | he | he <;>
        simp [localCellWeight, tableScorePoint, cellIndicator,
          oddMagnitude, evenMagnitude, ho, he]

private theorem orientationQuadraticTotal_eq_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    orientationQuadraticTotal (localTable f ell) =
      ∑ a : Vec, quadraticTotalPoint
        (oddMagnitude f (a + ell)) (evenMagnitude f a) := by
  have htable := weightedLocalTable_eq_sum f hf hnorm hall ell
    0 1 0 2 2 1 2 1 0
  calc
    orientationQuadraticTotal (localTable f ell) =
        weightedTableValue 0 1 0 2 2 1 2 1 0 (localTable f ell) := by
      norm_num [orientationQuadraticTotal, weightedTableValue]
    _ = ∑ a : Vec, localCellWeight 0 1 0 2 2 1 2 1 0
          (oddMagnitude f (a + ell)) (evenMagnitude f a) := htable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
          ho | ho | ho <;>
        rcases normalized_even_frequency_magnitude f hf hnorm hall a with
          he | he | he <;>
        simp [localCellWeight, quadraticTotalPoint, cellIndicator,
          oddMagnitude, evenMagnitude, ho, he]

private theorem twistedLowerSpectrum_parseval
    (f : V 8 -> ZMod 2) (ell : Vec) :
    (∑ a : Vec, twistedLowerSpectrum f ell a ^ 2) = 4096 := by
  calc
    _ = ∑ a : Vec, lowerSpectrum f ell a ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact twisted_lower_square_eq f ell a
    _ = 4096 := normalizedWalsh_parseval (orientedLowerSlice f ell)

private theorem twistedUpperSpectrum_parseval
    (f : V 8 -> ZMod 2) (ell : Vec) :
    (∑ a : Vec, twistedUpperSpectrum f ell a ^ 2) = 4096 := by
  calc
    _ = ∑ a : Vec, upperSpectrum f ell a ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact twisted_upper_square_eq f ell a
    _ = 4096 := normalizedWalsh_parseval (orientedUpperSlice f ell)

private theorem twistedLowerSpectrum_fourth_modeq
    (f : V 8 -> ZMod 2) (ell : Vec)
    (hodd : Odd (weight (orientedLowerSlice f ell))) :
    (∑ a : Vec, twistedLowerSpectrum f ell a ^ 4) ≡ 896 [ZMOD 1024] := by
  have heq :
      (∑ a : Vec, twistedLowerSpectrum f ell a ^ 4) =
        ∑ a : Vec, lowerSpectrum f ell a ^ 4 := by
    apply Finset.sum_congr rfl
    intro a _
    calc
      twistedLowerSpectrum f ell a ^ 4 =
          (twistedLowerSpectrum f ell a ^ 2) ^ 2 := by ring
      _ = (lowerSpectrum f ell a ^ 2) ^ 2 := by
        rw [twisted_lower_square_eq]
      _ = lowerSpectrum f ell a ^ 4 := by ring
  rw [heq]
  exact normalizedWalsh_fourth_moment_modeq
    (orientedLowerSlice f ell) hodd

private theorem twistedLowerSpectrum_natAbs_eq
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    (twistedLowerSpectrum f ell a).natAbs =
      (normalizedWalsh (orientedLowerSlice f ell) a).natAbs := by
  rw [twistedLowerSpectrum_eq, Int.natAbs_mul]
  rcases character_eq_one_or_neg_one a (commonShift f ell) with h | h <;>
    simp [h, lowerSpectrum]

private theorem twistedUpperSpectrum_natAbs_eq
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    (twistedUpperSpectrum f ell a).natAbs =
      (normalizedWalsh (orientedUpperSlice f ell) a).natAbs := by
  rw [twistedUpperSpectrum_eq, Int.natAbs_mul]
  rcases character_eq_one_or_neg_one a (commonShift f ell) with h | h <;>
    simp [h, upperSpectrum]

private theorem twistedLowerSpectrum_fourth_sum_eq
    (f : V 8 -> ZMod 2) (ell : Vec) :
    (∑ a : Vec, twistedLowerSpectrum f ell a ^ 4) =
      ∑ a : Vec, normalizedWalsh (orientedLowerSlice f ell) a ^ 4 := by
  apply Finset.sum_congr rfl
  intro a _
  calc
    twistedLowerSpectrum f ell a ^ 4 =
        (twistedLowerSpectrum f ell a ^ 2) ^ 2 := by ring
    _ = (lowerSpectrum f ell a ^ 2) ^ 2 := by
      rw [twisted_lower_square_eq]
    _ = normalizedWalsh (orientedLowerSlice f ell) a ^ 4 := by
      simp only [lowerSpectrum]
      ring

private theorem twistedUpperSpectrum_fourth_sum_eq
    (f : V 8 -> ZMod 2) (ell : Vec) :
    (∑ a : Vec, twistedUpperSpectrum f ell a ^ 4) =
      ∑ a : Vec, normalizedWalsh (orientedUpperSlice f ell) a ^ 4 := by
  apply Finset.sum_congr rfl
  intro a _
  calc
    twistedUpperSpectrum f ell a ^ 4 =
        (twistedUpperSpectrum f ell a ^ 2) ^ 2 := by ring
    _ = (upperSpectrum f ell a ^ 2) ^ 2 := by
      rw [twisted_upper_square_eq]
    _ = normalizedWalsh (orientedUpperSlice f ell) a ^ 4 := by
      simp only [upperSpectrum]
      ring

private theorem pairCount_left_le_absNineCount
    (P Q : Vec -> Int) (s : Nat) :
    pairCount P Q 9 s ≤ absNineCount P := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha.1

private theorem pairCount_right_le_absNineCount
    (P Q : Vec -> Int) (r : Nat) :
    pairCount P Q r 9 ≤ absNineCount Q := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha.2

private theorem local_extreme_le
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) : (localTable f ell).a ≤ 76 := by
  obtain ⟨eta, heta, hp, hq⟩ :=
    exists_orientation_residue f hf hnorm hall ell
  let P : Vec -> Int := twistedLowerSpectrum f ell
  let Q : Vec -> Int := twistedUpperSpectrum f ell
  have hfacts (a : Vec) :=
    local_orientation_point_facts f hf hnorm hall ell eta heta hp hq a
  have hsplit :
      pairCount P Q 9 1 + pairCount P Q 1 9 = (localTable f ell).a := by
    change pairCount P Q 9 1 + pairCount P Q 1 9 =
      localCellCount f ell 20 16
    apply pairCount_add_eq_localCellCount
    intro a
    simpa [P, Q] using (hfacts a).massA
  calc
    (localTable f ell).a = pairCount P Q 9 1 + pairCount P Q 1 9 :=
      hsplit.symm
    _ ≤ absNineCount P + absNineCount Q :=
      Nat.add_le_add (pairCount_left_le_absNineCount P Q 1)
        (pairCount_right_le_absNineCount P Q 1)
    _ ≤ 76 := by
      have hp9 := absNineCount_lower_le f hf hnorm hall ell
      have hq9 := absNineCount_upper_le f hf hnorm hall ell
      change absNineCount P ≤ 38 at hp9
      change absNineCount Q ≤ 38 at hq9
      omega

private theorem local_orientation_witness
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) : OrientationWitness (localTable f ell) := by
  obtain ⟨eta, heta, hp, hq⟩ :=
    exists_orientation_residue f hf hnorm hall ell
  let P : Vec -> Int := twistedLowerSpectrum f ell
  let Q : Vec -> Int := twistedUpperSpectrum f ell
  let da := pairDelta P Q 9 1
  let db := pairDelta P Q 7 3
  let dc := pairDelta P Q 7 1
  let de := pairDelta P Q 5 3
  let df := pairDelta P Q 5 1
  let dh := pairDelta P Q 3 1
  have hfacts (a : Vec) : OrientationPointFacts
      (P a) (Q a) (oddMagnitude f (a + ell)) (evenMagnitude f a) eta := by
    simpa [P, Q] using
      local_orientation_point_facts f hf hnorm hall ell eta heta hp hq a
  have hsplitA :
      pairCount P Q 9 1 + pairCount P Q 1 9 = (localTable f ell).a := by
    change pairCount P Q 9 1 + pairCount P Q 1 9 =
      localCellCount f ell 20 16
    exact pairCount_add_eq_localCellCount f ell P Q 9 1 20 16
      (fun a => (hfacts a).massA)
  have hsplitB :
      pairCount P Q 7 3 + pairCount P Q 3 7 = (localTable f ell).b := by
    change pairCount P Q 7 3 + pairCount P Q 3 7 =
      localCellCount f ell 20 8
    exact pairCount_add_eq_localCellCount f ell P Q 7 3 20 8
      (fun a => (hfacts a).massB)
  have hsplitC :
      pairCount P Q 7 1 + pairCount P Q 1 7 = (localTable f ell).c := by
    change pairCount P Q 7 1 + pairCount P Q 1 7 =
      localCellCount f ell 12 16
    exact pairCount_add_eq_localCellCount f ell P Q 7 1 12 16
      (fun a => (hfacts a).massC)
  have hsplitE :
      pairCount P Q 5 3 + pairCount P Q 3 5 = (localTable f ell).e := by
    change pairCount P Q 5 3 + pairCount P Q 3 5 =
      localCellCount f ell 4 16
    exact pairCount_add_eq_localCellCount f ell P Q 5 3 4 16
      (fun a => (hfacts a).massE)
  have hsplitF :
      pairCount P Q 5 1 + pairCount P Q 1 5 = (localTable f ell).f := by
    change pairCount P Q 5 1 + pairCount P Q 1 5 =
      localCellCount f ell 12 8
    exact pairCount_add_eq_localCellCount f ell P Q 5 1 12 8
      (fun a => (hfacts a).massF)
  have hsplitH :
      pairCount P Q 3 1 + pairCount P Q 1 3 = (localTable f ell).h := by
    change pairCount P Q 3 1 + pairCount P Q 1 3 =
      localCellCount f ell 4 8
    exact pairCount_add_eq_localCellCount f ell P Q 3 1 4 8
      (fun a => (hfacts a).massH)
  have hda : da ∈ deltas (localTable f ell).a := by
    dsimp [da]
    exact pairDelta_mem_deltas P Q 9 1 _ hsplitA
  have hdb : db ∈ deltas (localTable f ell).b := by
    dsimp [db]
    exact pairDelta_mem_deltas P Q 7 3 _ hsplitB
  have hdc : dc ∈ deltas (localTable f ell).c := by
    dsimp [dc]
    exact pairDelta_mem_deltas P Q 7 1 _ hsplitC
  have hde : de ∈ deltas (localTable f ell).e := by
    dsimp [de]
    exact pairDelta_mem_deltas P Q 5 3 _ hsplitE
  have hdf : df ∈ deltas (localTable f ell).f := by
    dsimp [df]
    exact pairDelta_mem_deltas P Q 5 1 _ hsplitF
  have hdh : dh ∈ deltas (localTable f ell).h := by
    dsimp [dh]
    exact pairDelta_mem_deltas P Q 3 1 _ hsplitH
  have henergy : orientationEnergy da db dc de df dh = 0 := by
    calc
      orientationEnergy da db dc de df dh =
          ∑ a : Vec, energyPoint (P a) (Q a) := by
        simpa [da, db, dc, de, df, dh] using
          orientationEnergy_pairDelta_eq_sum P Q
      _ = ∑ a : Vec, (P a ^ 2 - Q a ^ 2) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hfacts a).energy.symm
      _ = (∑ a : Vec, P a ^ 2) - ∑ a : Vec, Q a ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = 0 := by
        change
          (∑ a : Vec, twistedLowerSpectrum f ell a ^ 2) -
            ∑ a : Vec, twistedUpperSpectrum f ell a ^ 2 = 0
        rw [twistedLowerSpectrum_parseval, twistedUpperSpectrum_parseval]
        norm_num
  have hfourthEq :
      orientationFourth da db dc de df dh =
        (∑ a : Vec, P a ^ 4) - ∑ a : Vec, Q a ^ 4 := by
    calc
      orientationFourth da db dc de df dh =
          ∑ a : Vec, fourthPoint (P a) (Q a) := by
        simpa [da, db, dc, de, df, dh] using
          orientationFourth_pairDelta_eq_sum P Q
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hfacts a).fourth.symm
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hcombined :
      (fourthMoment (localTable f ell) : Int) =
        (∑ a : Vec, P a ^ 4) + ∑ a : Vec, Q a ^ 4 := by
    calc
      (fourthMoment (localTable f ell) : Int) =
          ∑ a : Vec,
            (normalizedWalsh (orientedLowerSlice f ell) a ^ 4 +
              normalizedWalsh (orientedUpperSlice f ell) a ^ 4) :=
        local_fourthMoment_as_sum f hf hnorm hall ell
      _ = (∑ a : Vec,
            normalizedWalsh (orientedLowerSlice f ell) a ^ 4) +
          ∑ a : Vec,
            normalizedWalsh (orientedUpperSlice f ell) a ^ 4 :=
        Finset.sum_add_distrib
      _ = _ := by
        rw [← twistedLowerSpectrum_fourth_sum_eq,
          ← twistedUpperSpectrum_fourth_sum_eq]
  have hoddSlices :=
    LeanCipher.BalancedEightSemanticScalar.oriented_slice_weights_odd
      f hf hnorm hall ell
  have hpFourth : (∑ a : Vec, P a ^ 4) % 1024 = 896 := by
    change (∑ a : Vec, twistedLowerSpectrum f ell a ^ 4) % 1024 = 896
    rw [twistedLowerSpectrum_fourth_sum_eq]
    exact normalizedWalsh_fourth_moment_mod
      (orientedLowerSlice f ell) hoddSlices.1
  have hfourth :
      orientationFourth da db dc de df dh % 2048 =
        (1792 - (fourthMoment (localTable f ell) : Int)) % 2048 := by
    rw [hfourthEq]
    omega
  have hpInv := pValue_inversion f ell 0
  have hqInv := qValue_inversion f ell 0
  simp only [character, f2Dot_zero_right, BooleanWalsh.sign_zero, mul_one, add_zero]
    at hpInv hqInv
  have hpInv' :
      (∑ a : Vec, P a) =
        64 * sign (orientedLowerSlice f ell (commonShift f ell)) := by
    simpa only [P, twistedLowerSpectrum] using hpInv
  have hqInv' :
      (∑ a : Vec, Q a) =
        64 * sign (orientedUpperSlice f ell (commonShift f ell)) := by
    simpa only [Q, twistedUpperSpectrum] using hqInv
  have htotalRelation :
      (∑ a : Vec, P a) - (∑ a : Vec, Q a) =
        eta * totalScore (localTable f ell) := by
    calc
      _ = ∑ a : Vec, (P a - Q a) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ a : Vec, eta * tableScorePoint
          (oddMagnitude f (a + ell)) (evenMagnitude f a) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hfacts a).totalScore
      _ = eta * ∑ a : Vec, tableScorePoint
          (oddMagnitude f (a + ell)) (evenMagnitude f a) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [← totalScore_eq_sum_tableScorePoint f hf hnorm hall ell]
  have horientationRelation :
      (∑ a : Vec, P a) + (∑ a : Vec, Q a) =
        eta * orientationScore da db dc de df dh := by
    calc
      _ = ∑ a : Vec, (P a + Q a) := Finset.sum_add_distrib.symm
      _ = ∑ a : Vec, eta * orientationPoint (P a) (Q a) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hfacts a).orientationScore
      _ = eta * ∑ a : Vec, orientationPoint (P a) (Q a) := by
        rw [Finset.mul_sum]
      _ = _ := by
        rw [orientationScore_pairDelta_eq_sum]
  have hsigned :
      SignedOrientationTarget (localTable f ell)
        (orientationScore da db dc de df dh) := by
    rcases heta with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one
        (orientedLowerSlice f ell (commonShift f ell)) with hl | hl <;>
      rcases zmod2_eq_zero_or_one
        (orientedUpperSlice f ell (commonShift f ell)) with hu | hu <;>
      simp [hl, hu] at hpInv' hqInv' <;>
      unfold SignedOrientationTarget <;>
      omega
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have hweightP :
      (weight (intParity (squareFirstBit g)) : Int) =
        ∑ a : Vec, absBit (P a) := by
    simpa only [absBit] using
      squareFirstBit_weight_eq_gamma_indicator_sum g
        (by simpa [g] using hoddSlices.1) P
        (fun a => by
          simpa [g, P] using twistedLowerSpectrum_natAbs_eq f ell a)
        (fun a => by
          change (twistedLowerSpectrum f ell a).natAbs ≤ 9
          exact (twisted_spectrum_natAbs_le_nine
            f hf hnorm hall ell a).1)
  have hweightQ :
      (weight (intParity (squareFirstBit h)) : Int) =
        ∑ a : Vec, absBit (Q a) := by
    simpa only [absBit] using
      squareFirstBit_weight_eq_gamma_indicator_sum h
        (by simpa [h] using hoddSlices.2) Q
        (fun a => by
          simpa [h, Q] using twistedUpperSpectrum_natAbs_eq f ell a)
        (fun a => by
          change (twistedUpperSpectrum f ell a).natAbs ≤ 9
          exact (twisted_spectrum_natAbs_le_nine
            f hf hnorm hall ell a).2)
  have hallowedP :
      (weight (intParity (squareFirstBit g)) : Int) ∈ quadraticWeightsInt :=
    squareFirstBit_weight_cast_mem_quadraticWeightsInt g
      (by simpa [g] using hoddSlices.1)
  have hallowedQ :
      (weight (intParity (squareFirstBit h)) : Int) ∈ quadraticWeightsInt :=
    squareFirstBit_weight_cast_mem_quadraticWeightsInt h
      (by simpa [h] using hoddSlices.2)
  have hquadLower :
      2 * (weight (intParity (squareFirstBit g)) : Int) =
        orientationQuadraticTotal (localTable f ell) +
          orientationQuadraticDifference db df dh := by
    calc
      _ = 2 * ∑ a : Vec, absBit (P a) := by rw [hweightP]
      _ = ∑ a : Vec, 2 * absBit (P a) := by rw [Finset.mul_sum]
      _ = ∑ a : Vec,
          (quadraticTotalPoint
              (oddMagnitude f (a + ell)) (evenMagnitude f a) +
            quadraticDifferencePoint (P a) (Q a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hfacts a).lowerQuadratic
      _ = (∑ a : Vec, quadraticTotalPoint
            (oddMagnitude f (a + ell)) (evenMagnitude f a)) +
          ∑ a : Vec, quadraticDifferencePoint (P a) (Q a) :=
        Finset.sum_add_distrib
      _ = _ := by
        rw [orientationQuadraticTotal_eq_sum f hf hnorm hall ell,
          orientationQuadraticDifference_pairDelta_eq_sum]
  have hquadUpper :
      2 * (weight (intParity (squareFirstBit h)) : Int) =
        orientationQuadraticTotal (localTable f ell) -
          orientationQuadraticDifference db df dh := by
    calc
      _ = 2 * ∑ a : Vec, absBit (Q a) := by rw [hweightQ]
      _ = ∑ a : Vec, 2 * absBit (Q a) := by rw [Finset.mul_sum]
      _ = ∑ a : Vec,
          (quadraticTotalPoint
              (oddMagnitude f (a + ell)) (evenMagnitude f a) -
            quadraticDifferencePoint (P a) (Q a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hfacts a).upperQuadratic
      _ = (∑ a : Vec, quadraticTotalPoint
            (oddMagnitude f (a + ell)) (evenMagnitude f a)) -
          ∑ a : Vec, quadraticDifferencePoint (P a) (Q a) :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [orientationQuadraticTotal_eq_sum f hf hnorm hall ell,
          orientationQuadraticDifference_pairDelta_eq_sum]
  have hevenQuadratic :
      (orientationQuadraticTotal (localTable f ell) +
        orientationQuadraticDifference db df dh) % 2 = 0 := by
    omega
  have hfirst :
      firstOrientedQuadraticWeight (localTable f ell) db df dh =
        (weight (intParity (squareFirstBit g)) : Int) := by
    unfold firstOrientedQuadraticWeight
    omega
  have hsecond :
      secondOrientedQuadraticWeight (localTable f ell) db df dh =
        (weight (intParity (squareFirstBit h)) : Int) := by
    unfold secondOrientedQuadraticWeight
    rw [hfirst]
    omega
  refine ⟨da, db, dc, de, df, dh,
    hda, hdb, hdc, hde, hdf, hdh,
    henergy, hfourth, hsigned, hevenQuadratic, ?_, ?_⟩
  · rw [hfirst]
    exact hallowedP
  · rw [hsecond]
    exact hallowedQ

theorem localTable_semantic_conditions
    (f : V 8 -> ZMod 2)
    (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a, (walsh f a).natAbs <= 20)
    (ell : V 7) :
    SemanticLocalConditions (directionWeight f ell) (localTable f ell) := by
  obtain ⟨hweight, hsum, hdistinguished, hsecond, hproductWeight,
      hproductDivisible, hfourth⟩ :=
    semantic_scalar_conditions f hf hnorm hall ell
  exact
    { weight_allowed := hweight
      table_sum := hsum
      distinguished_positive := hdistinguished
      extreme_le := local_extreme_le f hf hnorm hall ell
      combined_second_moment := hsecond
      product_first_bit_weight := hproductWeight
      product_transform_divisible := hproductDivisible
      combined_fourth_congruence := hfourth
      orientation := local_orientation_witness f hf hnorm hall ell }

end LeanCipher.BalancedEightSemantic

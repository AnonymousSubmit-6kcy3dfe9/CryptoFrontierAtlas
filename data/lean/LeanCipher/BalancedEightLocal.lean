import LeanCipher.BalancedEightNormalize
import LeanCipher.BalancedEightCertificates
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEightCertificates

/-!
# Magnitude classes and local contingency tables

After support-XOR normalization, normalized Walsh parity separates the spectrum
into the even magnitudes `0,8,16` and odd magnitudes `4,12,20`.  This file
defines the global six-entry profile and the nine-entry table attached to an
odd direction.
-/

private theorem natAbs_eq_zero_or_two_or_four_of_even_le_five
    {q : Int} (hq : q.natAbs ≤ 5) (heven : (2 : Int) ∣ q) :
    q.natAbs = 0 ∨ q.natAbs = 2 ∨ q.natAbs = 4 := by
  obtain ⟨k, rfl⟩ := heven
  rw [Int.natAbs_mul] at hq ⊢
  norm_num at hq ⊢
  omega

private theorem natAbs_eq_one_or_three_or_five_of_odd_le_five
    {q : Int} (hq : q.natAbs ≤ 5) (hodd : (2 : Int) ∣ q - 1) :
    q.natAbs = 1 ∨ q.natAbs = 3 ∨ q.natAbs = 5 := by
  obtain ⟨k, hk⟩ := hodd
  have hqform : q = 2 * k + 1 := by omega
  have hbounds : -5 ≤ q ∧ q ≤ 5 := by
    constructor <;> omega
  omega

theorem magnitude_class_even_normalized
    {z : Int} (hdiv : (4 : Int) ∣ z) (hle : z.natAbs ≤ 20)
    (hparity : ((z / 4 : Int) : ZMod 2) = 0) :
    z.natAbs = 0 ∨ z.natAbs = 8 ∨ z.natAbs = 16 := by
  obtain ⟨q, rfl⟩ := hdiv
  have hcancel : (4 * q : Int) / 4 = q := by omega
  rw [hcancel] at hparity
  have heven : (2 : Int) ∣ q :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd q 2).mp hparity
  have hq : q.natAbs ≤ 5 := by
    rw [Int.natAbs_mul] at hle
    norm_num at hle
    omega
  rcases natAbs_eq_zero_or_two_or_four_of_even_le_five hq heven with h | h | h
  · left
    rw [Int.natAbs_mul, h]
    norm_num
  · right; left
    rw [Int.natAbs_mul, h]
    norm_num
  · right; right
    rw [Int.natAbs_mul, h]
    norm_num

theorem magnitude_class_odd_normalized
    {z : Int} (hdiv : (4 : Int) ∣ z) (hle : z.natAbs ≤ 20)
    (hparity : ((z / 4 : Int) : ZMod 2) = 1) :
    z.natAbs = 4 ∨ z.natAbs = 12 ∨ z.natAbs = 20 := by
  obtain ⟨q, rfl⟩ := hdiv
  have hcancel : (4 * q : Int) / 4 = q := by omega
  rw [hcancel] at hparity
  have hoddCast : (((q - 1 : Int) : ZMod 2)) = 0 := by
    rw [Int.cast_sub, hparity]
    norm_num
  have hodd : (2 : Int) ∣ q - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (q - 1) 2).mp hoddCast
  have hq : q.natAbs ≤ 5 := by
    rw [Int.natAbs_mul] at hle
    norm_num at hle
    omega
  rcases natAbs_eq_one_or_three_or_five_of_odd_le_five hq hodd with h | h | h
  · left
    rw [Int.natAbs_mul, h]
    norm_num
  · right; left
    rw [Int.natAbs_mul, h]
    norm_num
  · right; right
    rw [Int.natAbs_mul, h]
    norm_num

theorem normalized_even_frequency_magnitude
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (a : V 7) :
    (walsh f (join a 0)).natAbs = 0 ∨
      (walsh f (join a 0)).natAbs = 8 ∨
      (walsh f (join a 0)).natAbs = 16 := by
  apply magnitude_class_even_normalized
  · exact four_dvd_all_walsh_of_balanced f hf (join a 0)
  · exact hall (join a 0)
  · rw [normalized_walsh_parity f hf, hnorm, lastBasis_eq_join,
      f2Dot_join]
    simp

theorem normalized_odd_frequency_magnitude
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (a : V 7) :
    (walsh f (join a 1)).natAbs = 4 ∨
      (walsh f (join a 1)).natAbs = 12 ∨
      (walsh f (join a 1)).natAbs = 20 := by
  apply magnitude_class_odd_normalized
  · exact four_dvd_all_walsh_of_balanced f hf (join a 1)
  · exact hall (join a 1)
  · rw [normalized_walsh_parity f hf, hnorm, lastBasis_eq_join,
      f2Dot_join]
    simp

def evenMagnitude (f : V 8 -> ZMod 2) (a : V 7) : Nat :=
  (walsh f (join a 0)).natAbs

def oddMagnitude (f : V 8 -> ZMod 2) (a : V 7) : Nat :=
  (walsh f (join a 1)).natAbs

def magnitudeCount (spectrum : V 7 -> Nat) (m : Nat) : Nat :=
  ((Finset.univ : Finset (V 7)).filter fun a => spectrum a = m).card

def spectralProfile (f : V 8 -> ZMod 2) : Profile :=
  { n20 := magnitudeCount (oddMagnitude f) 20
  , n12 := magnitudeCount (oddMagnitude f) 12
  , n4 := magnitudeCount (oddMagnitude f) 4
  , n16 := magnitudeCount (evenMagnitude f) 16
  , n8 := magnitudeCount (evenMagnitude f) 8
  , n0 := magnitudeCount (evenMagnitude f) 0 }

def localCellCount (f : V 8 -> ZMod 2) (ell : V 7)
    (odd even : Nat) : Nat :=
  ((Finset.univ : Finset (V 7)).filter fun a =>
    oddMagnitude f (a + ell) = odd ∧ evenMagnitude f a = even).card

def localTable (f : V 8 -> ZMod 2) (ell : V 7) : LocalTable :=
  { a := localCellCount f ell 20 16
  , b := localCellCount f ell 20 8
  , c := localCellCount f ell 12 16
  , d := localCellCount f ell 20 0
  , e := localCellCount f ell 4 16
  , f := localCellCount f ell 12 8
  , g := localCellCount f ell 12 0
  , h := localCellCount f ell 4 8
  , i := localCellCount f ell 4 0 }

theorem magnitudeCount_eq_sum_indicator
    (spectrum : V 7 -> Nat) (m : Nat) :
    magnitudeCount spectrum m =
      ∑ a : V 7, if spectrum a = m then 1 else 0 := by
  symm
  simp [magnitudeCount, Finset.sum_boole]

theorem localCellCount_eq_sum_indicator
    (f : V 8 -> ZMod 2) (ell : V 7) (odd even : Nat) :
    localCellCount f ell odd even =
      ∑ a : V 7,
        if oddMagnitude f (a + ell) = odd ∧ evenMagnitude f a = even
        then 1 else 0 := by
  symm
  simp [localCellCount, Finset.sum_boole]

theorem localTable_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    tableSum (localTable f ell) = 128 := by
  change
    localCellCount f ell 20 16 + localCellCount f ell 20 8 +
      localCellCount f ell 12 16 + localCellCount f ell 20 0 +
      localCellCount f ell 4 16 + localCellCount f ell 12 8 +
      localCellCount f ell 12 0 + localCellCount f ell 4 8 +
      localCellCount f ell 4 0 = 128
  simp_rw [localCellCount_eq_sum_indicator]
  rw [← show (∑ _a : V 7, (1 : Nat)) = 128 by
    norm_num [f2Vec_card]]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
      ho | ho | ho <;>
    rcases normalized_even_frequency_magnitude f hf hnorm hall a with
      he | he | he <;>
    simp [oddMagnitude, evenMagnitude, ho, he]

theorem sum_indicator_add_right (p : V 7 -> Prop) [DecidablePred p]
    (ell : V 7) :
    (∑ a : V 7, if p (a + ell) then (1 : Nat) else 0) =
      ∑ a : V 7, if p a then 1 else 0 := by
  exact Fintype.sum_equiv (Equiv.addRight ell)
    (fun a : V 7 => if p (a + ell) then (1 : Nat) else 0)
    (fun a : V 7 => if p a then (1 : Nat) else 0) (fun _ => rfl)

theorem localTable_row_count
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell : V 7) (m : Nat) :
    localCellCount f ell m 16 + localCellCount f ell m 8 +
      localCellCount f ell m 0 = magnitudeCount (oddMagnitude f) m := by
  simp_rw [localCellCount_eq_sum_indicator]
  repeat rw [← Finset.sum_add_distrib]
  rw [magnitudeCount_eq_sum_indicator]
  calc
    (∑ a : V 7,
        ((if oddMagnitude f (a + ell) = m ∧ evenMagnitude f a = 16 then 1 else 0) +
          (if oddMagnitude f (a + ell) = m ∧ evenMagnitude f a = 8 then 1 else 0) +
          if oddMagnitude f (a + ell) = m ∧ evenMagnitude f a = 0 then 1 else 0)) =
        ∑ a : V 7, if oddMagnitude f (a + ell) = m then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rcases normalized_even_frequency_magnitude f hf hnorm hall a with
          he | he | he <;>
        simp [evenMagnitude, he]
    _ = ∑ a : V 7, if oddMagnitude f a = m then 1 else 0 := by
      exact sum_indicator_add_right (fun a => oddMagnitude f a = m) ell

theorem localTable_column_count
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell : V 7) (m : Nat) :
    localCellCount f ell 20 m + localCellCount f ell 12 m +
      localCellCount f ell 4 m = magnitudeCount (evenMagnitude f) m := by
  simp_rw [localCellCount_eq_sum_indicator]
  repeat rw [← Finset.sum_add_distrib]
  rw [magnitudeCount_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro a _
  rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
      ho | ho | ho <;>
    simp [oddMagnitude, ho]

theorem localTable_margins
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    margins (localTable f ell) = spectralProfile f := by
  simp only [margins, localTable, spectralProfile]
  congr 1
  · exact localTable_row_count f hf hnorm hall ell 20
  · exact localTable_row_count f hf hnorm hall ell 12
  · exact localTable_row_count f hf hnorm hall ell 4
  · exact localTable_column_count f hf hnorm hall ell 16
  · exact localTable_column_count f hf hnorm hall ell 8
  · exact localTable_column_count f hf hnorm hall ell 0

def orientedLowerSlice (f : V 8 -> ZMod 2) (ell : V 7) :
    V 7 -> ZMod 2 :=
  if 0 < walsh f (join ell 1) then directionLowerSlice f ell
  else directionUpperSlice f ell

def orientedUpperSlice (f : V 8 -> ZMod 2) (ell : V 7) :
    V 7 -> ZMod 2 :=
  if 0 < walsh f (join ell 1) then directionUpperSlice f ell
  else directionLowerSlice f ell

theorem oriented_slice_sum (f : V 8 -> ZMod 2) (ell a : V 7) :
    walsh f (join a 0) =
      walsh (orientedLowerSlice f ell) a +
        walsh (orientedUpperSlice f ell) a := by
  by_cases h : 0 < walsh f (join ell 1)
  · simpa [orientedLowerSlice, orientedUpperSlice, h] using
      direction_slice_sum f ell a
  · rw [orientedLowerSlice, orientedUpperSlice, if_neg h, if_neg h,
      add_comm]
    exact direction_slice_sum f ell a

theorem oriented_slice_difference_abs
    (f : V 8 -> ZMod 2) (ell a : V 7)
    (_hne : walsh f (join (a + ell) 1) ≠ 0) :
    (walsh (orientedLowerSlice f ell) a -
        walsh (orientedUpperSlice f ell) a).natAbs =
      (walsh f (join (a + ell) 1)).natAbs := by
  by_cases h : 0 < walsh f (join ell 1)
  · simp only [orientedLowerSlice, orientedUpperSlice, if_pos h]
    rw [← direction_slice_difference f ell a]
  · simp only [orientedLowerSlice, orientedUpperSlice, if_neg h]
    rw [show walsh (directionUpperSlice f ell) a -
        walsh (directionLowerSlice f ell) a =
          -(walsh (directionLowerSlice f ell) a -
            walsh (directionUpperSlice f ell) a) by ring]
    rw [Int.natAbs_neg, ← direction_slice_difference f ell a]

theorem normalized_odd_frequency_ne_zero
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (a : V 7) :
    walsh f (join a 1) ≠ 0 := by
  intro hzero
  have hclass := normalized_odd_frequency_magnitude f hf hnorm hall a
  simp [hzero] at hclass

theorem oriented_slice_difference_zero
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    walsh (orientedLowerSlice f ell) 0 -
        walsh (orientedUpperSlice f ell) 0 = oddMagnitude f ell := by
  have hne := normalized_odd_frequency_ne_zero f hf hnorm hall ell
  have hraw := direction_slice_difference f ell 0
  simp only [zero_add] at hraw
  by_cases h : 0 < walsh f (join ell 1)
  · simp only [orientedLowerSlice, orientedUpperSlice, if_pos h]
    rw [← hraw]
    simp [oddMagnitude, Int.natAbs_of_nonneg (le_of_lt h)]
  · have hneg : walsh f (join ell 1) < 0 := by omega
    simp only [orientedLowerSlice, orientedUpperSlice, if_neg h]
    rw [show walsh (directionUpperSlice f ell) 0 -
        walsh (directionLowerSlice f ell) 0 =
          -(walsh (directionLowerSlice f ell) 0 -
            walsh (directionUpperSlice f ell) 0) by ring]
    rw [← hraw]
    simp [oddMagnitude, Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)]

theorem oriented_slice_sum_zero
    (f : V 8 -> ZMod 2) (hf : weight f = 128) (ell : V 7) :
    walsh (orientedLowerSlice f ell) 0 +
      walsh (orientedUpperSlice f ell) 0 = 0 := by
  have hsum := oriented_slice_sum f ell 0
  have hjoin : join (0 : V 7) 0 = (0 : V 8) := by native_decide
  rw [hjoin, walsh_zero_of_balanced f hf] at hsum
  exact hsum.symm

theorem oriented_slice_weights
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    (oddMagnitude f ell = 20 ∧
      weight (orientedLowerSlice f ell) = 59 ∧
      weight (orientedUpperSlice f ell) = 69) ∨
    (oddMagnitude f ell = 12 ∧
      weight (orientedLowerSlice f ell) = 61 ∧
      weight (orientedUpperSlice f ell) = 67) ∨
    (oddMagnitude f ell = 4 ∧
      weight (orientedLowerSlice f ell) = 63 ∧
      weight (orientedUpperSlice f ell) = 65) := by
  have hsum := oriented_slice_sum_zero f hf ell
  have hdiff := oriented_slice_difference_zero f hf hnorm hall ell
  have hg := walsh_zero_eq_card_sub_two_weight (orientedLowerSlice f ell)
  have hh := walsh_zero_eq_card_sub_two_weight (orientedUpperSlice f ell)
  norm_num at hg hh
  rcases normalized_odd_frequency_magnitude f hf hnorm hall ell with
      hm | hm | hm
  · have hom : oddMagnitude f ell = 4 := by
      simpa [oddMagnitude] using hm
    rw [hom] at hdiff
    right; right
    exact ⟨hom, by omega, by omega⟩
  · have hom : oddMagnitude f ell = 12 := by
      simpa [oddMagnitude] using hm
    rw [hom] at hdiff
    right; left
    exact ⟨hom, by omega, by omega⟩
  · have hom : oddMagnitude f ell = 20 := by
      simpa [oddMagnitude] using hm
    rw [hom] at hdiff
    left
    exact ⟨hom, by omega, by omega⟩

def directionWeight (f : V 8 -> ZMod 2) (ell : V 7) : Nat :=
  weight (orientedLowerSlice f ell)

theorem directionWeight_mem
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    directionWeight f ell = 59 ∨ directionWeight f ell = 61 ∨
      directionWeight f ell = 63 := by
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h
  · exact Or.inl h.2.1
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inr h.2.1)

end LeanCipher.BalancedEight

import LeanCipher.BalancedEightEnumerationSound
import LeanCipher.BalancedEightGlobal
import LeanCipher.BalancedEightFamilyBridge
import LeanCipher.BalancedEightProfileElimination
import Mathlib

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEightCertificates

/-!
# From local semantic conditions to a surviving global profile

This module contains no Fourier input beyond the hypotheses displayed in its
main theorem.  It packages the list-theoretic and double-counting bridges used
after every real local table has been shown to satisfy the semantic enumerator
conditions.
-/

theorem exists_oddMagnitude_twenty_of_spectrum_twenty
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (hexists : ∃ a : V 8, (walsh f a).natAbs = 20) :
    ∃ ell : V 7, oddMagnitude f ell = 20 := by
  obtain ⟨a, ha⟩ := hexists
  rcases zmod2_eq_zero_or_one (last a) with hlast | hlast
  · have heven := normalized_even_frequency_magnitude
      f hf hnorm hall (head a)
    have haJoin : join (head a) 0 = a := by
      rw [← hlast]
      exact join_head_last a
    rw [haJoin, ha] at heven
    omega
  · refine ⟨head a, ?_⟩
    have haJoin : join (head a) 1 = a := by
      rw [← hlast]
      exact join_head_last a
    simpa [oddMagnitude, haJoin] using ha

private theorem exists_of_magnitudeCount_pos
    (spectrum : V 7 -> Nat) (m : Nat)
    (h : 0 < magnitudeCount spectrum m) :
    ∃ a : V 7, spectrum a = m := by
  unfold magnitudeCount at h
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

theorem local_declared_entry_of_semantic
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell : V 7)
    (hsemantic :
      SemanticLocalConditions (directionWeight f ell) (localTable f ell)) :
    (directionWeight f ell, spectralProfile f, localTable f ell) ∈
      declaredEntries := by
  have hentry := hsemantic.mem_declaredEntries
  rw [localTable_margins f hf hnorm hall ell] at hentry
  exact hentry

theorem directionColumn_mem_columns_of_semantic
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (ell : V 7)
    (hsemantic :
      SemanticLocalConditions (directionWeight f ell) (localTable f ell)) :
    directionColumn f ell ∈ columns (spectralProfile f) := by
  unfold directionColumn
  exact declaredEntry_column_mem
    (directionWeight f ell) (spectralProfile f) (localTable f ell)
    (local_declared_entry_of_semantic
      f hf hnorm hall ell hsemantic)

theorem spectralProfile_mem_declaredSurvivors_of_semantic
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (hexists : ∃ a : V 8, (walsh f a).natAbs = 20)
    (hsemantic : ∀ ell : V 7,
      SemanticLocalConditions (directionWeight f ell) (localTable f ell)) :
    spectralProfile f ∈ declaredSurvivors := by
  have hoddTwenty : ∃ ell : V 7, oddMagnitude f ell = 20 :=
    exists_oddMagnitude_twenty_of_spectrum_twenty
      f hf hnorm hall hexists
  have hprofile : spectralProfile f ∈ profiles59 := by
    obtain ⟨ell, hm⟩ := hoddTwenty
    have hw : directionWeight f ell = 59 :=
      (directionWeight_eq_59_iff f hf hnorm hall ell).2 hm
    have hentry := local_declared_entry_of_semantic
      f hf hnorm hall ell (hsemantic ell)
    rw [hw] at hentry
    exact profile_mem_profiles59_of_declaredEntry hentry
  have hfamilies : missingFamily (spectralProfile f) = false := by
    apply missingFamily_eq_false_of_declaredEntry_providers
    · intro hn12
      change 0 < magnitudeCount (oddMagnitude f) 12 at hn12
      obtain ⟨ell, hm⟩ := exists_of_magnitudeCount_pos
        (oddMagnitude f) 12 hn12
      have hw : directionWeight f ell = 61 :=
        (directionWeight_eq_61_iff f hf hnorm hall ell).2 hm
      refine ⟨localTable f ell, ?_⟩
      have hentry := local_declared_entry_of_semantic
        f hf hnorm hall ell (hsemantic ell)
      simpa [hw] using hentry
    · intro hn4
      change 0 < magnitudeCount (oddMagnitude f) 4 at hn4
      obtain ⟨ell, hm⟩ := exists_of_magnitudeCount_pos
        (oddMagnitude f) 4 hn4
      have hw : directionWeight f ell = 63 :=
        (directionWeight_eq_63_iff f hf hnorm hall ell).2 hm
      refine ⟨localTable f ell, ?_⟩
      have hentry := local_declared_entry_of_semantic
        f hf hnorm hall ell (hsemantic ell)
      simpa [hw] using hentry
  have hsolution :
      HasNonnegativeRationalSolution (spectralProfile f) := by
    apply directionColumns_give_nonnegative_rational_solution
      f hf hnorm hall
    intro ell
    exact directionColumn_mem_columns_of_semantic
      f hf hnorm hall ell (hsemantic ell)
  exact mem_declaredSurvivors_of_profile_constraints
    hprofile hfamilies hsolution

end LeanCipher.BalancedEight

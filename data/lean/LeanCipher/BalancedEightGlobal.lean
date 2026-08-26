import LeanCipher.BalancedEightLocal
import LeanCipher.BalancedEightFarkasSound
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEightCertificates

/-!
# Global double counting and certificate aggregation

This file connects the local table attached to each odd direction with the
twelve global equations used by the exact Farkas certificates.
-/

theorem sum_localCellCount
    (f : V 8 -> ZMod 2) (odd even : Nat) :
    (∑ ell : V 7, localCellCount f ell odd even) =
      magnitudeCount (oddMagnitude f) odd *
        magnitudeCount (evenMagnitude f) even := by
  classical
  simp_rw [localCellCount_eq_sum_indicator]
  rw [Finset.sum_comm]
  calc
    (∑ a : V 7, ∑ ell : V 7,
        if oddMagnitude f (a + ell) = odd /\ evenMagnitude f a = even
        then 1 else 0) =
        ∑ a : V 7,
          if evenMagnitude f a = even then
            magnitudeCount (oddMagnitude f) odd
          else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : evenMagnitude f a = even
      · simp only [ha, and_true, if_true]
        rw [magnitudeCount_eq_sum_indicator]
        simpa [add_comm] using
          (sum_indicator_add_right
            (fun x : V 7 => oddMagnitude f x = odd) a)
      · simp [ha]
    _ = magnitudeCount (oddMagnitude f) odd *
        magnitudeCount (evenMagnitude f) even := by
      rw [magnitudeCount_eq_sum_indicator (evenMagnitude f) even]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : evenMagnitude f a = even <;> simp [ha]

theorem sum_localTable_a (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).a) =
      (spectralProfile f).n20 * (spectralProfile f).n16 := by
  exact sum_localCellCount f 20 16

theorem sum_localTable_b (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).b) =
      (spectralProfile f).n20 * (spectralProfile f).n8 := by
  exact sum_localCellCount f 20 8

theorem sum_localTable_d (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).d) =
      (spectralProfile f).n20 * (spectralProfile f).n0 := by
  exact sum_localCellCount f 20 0

theorem sum_localTable_c (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).c) =
      (spectralProfile f).n12 * (spectralProfile f).n16 := by
  exact sum_localCellCount f 12 16

theorem sum_localTable_f (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).f) =
      (spectralProfile f).n12 * (spectralProfile f).n8 := by
  exact sum_localCellCount f 12 8

theorem sum_localTable_g (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).g) =
      (spectralProfile f).n12 * (spectralProfile f).n0 := by
  exact sum_localCellCount f 12 0

theorem sum_localTable_e (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).e) =
      (spectralProfile f).n4 * (spectralProfile f).n16 := by
  exact sum_localCellCount f 4 16

theorem sum_localTable_h (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).h) =
      (spectralProfile f).n4 * (spectralProfile f).n8 := by
  exact sum_localCellCount f 4 8

theorem sum_localTable_i (f : V 8 -> ZMod 2) :
    (∑ ell : V 7, (localTable f ell).i) =
      (spectralProfile f).n4 * (spectralProfile f).n0 := by
  exact sum_localCellCount f 4 0

def ownerForWeight (w : Nat) : Nat :=
  if w = 59 then 0 else if w = 61 then 1 else 2

def directionOwner (f : V 8 -> ZMod 2) (ell : V 7) : Nat :=
  ownerForWeight (directionWeight f ell)

def directionColumn (f : V 8 -> ZMod 2) (ell : V 7) : List Int :=
  column (directionOwner f ell) (localTable f ell)

theorem directionWeight_eq_59_iff
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    directionWeight f ell = 59 ↔ oddMagnitude f ell = 20 := by
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h
  · simp [directionWeight, h.1, h.2.1]
  · simp [directionWeight, h.1, h.2.1]
  · simp [directionWeight, h.1, h.2.1]

theorem directionWeight_eq_61_iff
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    directionWeight f ell = 61 ↔ oddMagnitude f ell = 12 := by
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h
  · simp [directionWeight, h.1, h.2.1]
  · simp [directionWeight, h.1, h.2.1]
  · simp [directionWeight, h.1, h.2.1]

theorem directionWeight_eq_63_iff
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    directionWeight f ell = 63 ↔ oddMagnitude f ell = 4 := by
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h
  · simp [directionWeight, h.1, h.2.1]
  · simp [directionWeight, h.1, h.2.1]
  · simp [directionWeight, h.1, h.2.1]

theorem directionOwner_eq_zero_iff
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    directionOwner f ell = 0 ↔ oddMagnitude f ell = 20 := by
  have h59 := directionWeight_eq_59_iff f hf hnorm hall ell
  rcases directionWeight_mem f hf hnorm hall ell with h | h | h <;>
    simp [directionOwner, ownerForWeight, h] at h59 ⊢ <;> omega

theorem directionOwner_eq_one_iff
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    directionOwner f ell = 1 ↔ oddMagnitude f ell = 12 := by
  have h61 := directionWeight_eq_61_iff f hf hnorm hall ell
  rcases directionWeight_mem f hf hnorm hall ell with h | h | h <;>
    simp [directionOwner, ownerForWeight, h] at h61 ⊢ <;> omega

theorem directionOwner_eq_two_iff
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) (ell : V 7) :
    directionOwner f ell = 2 ↔ oddMagnitude f ell = 4 := by
  have h63 := directionWeight_eq_63_iff f hf hnorm hall ell
  rcases directionWeight_mem f hf hnorm hall ell with h | h | h <;>
    simp [directionOwner, ownerForWeight, h] at h63 ⊢ <;> omega

theorem sum_directionOwner_zero
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) :
    (∑ ell : V 7, if directionOwner f ell = 0 then 1 else 0) =
      (spectralProfile f).n20 := by
  change _ = magnitudeCount (oddMagnitude f) 20
  rw [magnitudeCount_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro ell _
  simp only [directionOwner_eq_zero_iff f hf hnorm hall ell]

theorem sum_directionOwner_one
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) :
    (∑ ell : V 7, if directionOwner f ell = 1 then 1 else 0) =
      (spectralProfile f).n12 := by
  change _ = magnitudeCount (oddMagnitude f) 12
  rw [magnitudeCount_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro ell _
  simp only [directionOwner_eq_one_iff f hf hnorm hall ell]

theorem sum_directionOwner_two
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20) :
    (∑ ell : V 7, if directionOwner f ell = 2 then 1 else 0) =
      (spectralProfile f).n4 := by
  change _ = magnitudeCount (oddMagnitude f) 4
  rw [magnitudeCount_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro ell _
  simp only [directionOwner_eq_two_iff f hf hnorm hall ell]

theorem declaredEntry_column_mem
    (w : Nat) (profile : Profile) (table : LocalTable)
    (hentry : (w, profile, table) ∈ declaredEntries) :
    column (ownerForWeight w) table ∈ columns profile := by
  have hall : declaredEntries.all (fun entry =>
      decide (column (ownerForWeight entry.1) entry.2.2 ∈
        columns entry.2.1)) = true := by
    native_decide
  exact of_decide_eq_true ((List.all_eq_true.mp hall) _ hentry)

private theorem cast_nat_sum {g : V 7 -> Nat} {n : Nat}
    (h : (∑ x : V 7, g x) = n) :
    (∑ x : V 7, (g x : Int)) = (n : Int) := by
  rw [← Nat.cast_sum]
  exact congrArg (fun m : Nat => (m : Int)) h

private theorem valueAt_column_0 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (0 : Fin 12) =
      ((if owner = 0 then 1 else 0 : Nat) : Int) := by
  by_cases h : owner = 0 <;> simp [column, valueAt, h]

private theorem valueAt_column_1 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (1 : Fin 12) =
      ((if owner = 1 then 1 else 0 : Nat) : Int) := by
  by_cases h : owner = 1 <;> simp [column, valueAt, h]

private theorem valueAt_column_2 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (2 : Fin 12) =
      ((if owner = 2 then 1 else 0 : Nat) : Int) := by
  by_cases h : owner = 2 <;> simp [column, valueAt, h]

private theorem valueAt_column_3 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (3 : Fin 12) = table.a := rfl

private theorem valueAt_column_4 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (4 : Fin 12) = table.b := rfl

private theorem valueAt_column_5 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (5 : Fin 12) = table.d := rfl

private theorem valueAt_column_6 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (6 : Fin 12) = table.c := rfl

private theorem valueAt_column_7 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (7 : Fin 12) = table.f := rfl

private theorem valueAt_column_8 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (8 : Fin 12) = table.g := rfl

private theorem valueAt_column_9 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (9 : Fin 12) = table.e := rfl

private theorem valueAt_column_10 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (10 : Fin 12) = table.h := rfl

private theorem valueAt_column_11 (owner : Nat) (table : LocalTable) :
    valueAt (column owner table) (11 : Fin 12) = table.i := rfl

private theorem valueAt_rhs_0 (profile : Profile) :
    valueAt (rhs profile) (0 : Fin 12) = profile.n20 := rfl

private theorem valueAt_rhs_1 (profile : Profile) :
    valueAt (rhs profile) (1 : Fin 12) = profile.n12 := rfl

private theorem valueAt_rhs_2 (profile : Profile) :
    valueAt (rhs profile) (2 : Fin 12) = profile.n4 := rfl

private theorem valueAt_rhs_3 (profile : Profile) :
    valueAt (rhs profile) (3 : Fin 12) =
      ((profile.n20 * profile.n16 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_4 (profile : Profile) :
    valueAt (rhs profile) (4 : Fin 12) =
      ((profile.n20 * profile.n8 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_5 (profile : Profile) :
    valueAt (rhs profile) (5 : Fin 12) =
      ((profile.n20 * profile.n0 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_6 (profile : Profile) :
    valueAt (rhs profile) (6 : Fin 12) =
      ((profile.n12 * profile.n16 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_7 (profile : Profile) :
    valueAt (rhs profile) (7 : Fin 12) =
      ((profile.n12 * profile.n8 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_8 (profile : Profile) :
    valueAt (rhs profile) (8 : Fin 12) =
      ((profile.n12 * profile.n0 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_9 (profile : Profile) :
    valueAt (rhs profile) (9 : Fin 12) =
      ((profile.n4 * profile.n16 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_10 (profile : Profile) :
    valueAt (rhs profile) (10 : Fin 12) =
      ((profile.n4 * profile.n8 : Nat) : Int) := by
  norm_cast

private theorem valueAt_rhs_11 (profile : Profile) :
    valueAt (rhs profile) (11 : Fin 12) =
      ((profile.n4 * profile.n0 : Nat) : Int) := by
  norm_cast

theorem sum_directionColumn_coordinate_int
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (coordinate : Fin 12) :
    (∑ ell : V 7, valueAt (directionColumn f ell) coordinate) =
      valueAt (rhs (spectralProfile f)) coordinate := by
  rcases coordinate with ⟨i, hi⟩
  interval_cases i
  · have hc : (⟨0, hi⟩ : Fin 12) = (0 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_0]
    simp_rw [directionColumn, valueAt_column_0]
    exact cast_nat_sum (sum_directionOwner_zero f hf hnorm hall)
  · have hc : (⟨1, hi⟩ : Fin 12) = (1 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_1]
    simp_rw [directionColumn, valueAt_column_1]
    exact cast_nat_sum (sum_directionOwner_one f hf hnorm hall)
  · have hc : (⟨2, hi⟩ : Fin 12) = (2 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_2]
    simp_rw [directionColumn, valueAt_column_2]
    exact cast_nat_sum (sum_directionOwner_two f hf hnorm hall)
  · have hc : (⟨3, hi⟩ : Fin 12) = (3 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_3]
    simp_rw [directionColumn, valueAt_column_3]
    exact cast_nat_sum (sum_localTable_a f)
  · have hc : (⟨4, hi⟩ : Fin 12) = (4 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_4]
    simp_rw [directionColumn, valueAt_column_4]
    exact cast_nat_sum (sum_localTable_b f)
  · have hc : (⟨5, hi⟩ : Fin 12) = (5 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_5]
    simp_rw [directionColumn, valueAt_column_5]
    exact cast_nat_sum (sum_localTable_d f)
  · have hc : (⟨6, hi⟩ : Fin 12) = (6 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_6]
    simp_rw [directionColumn, valueAt_column_6]
    exact cast_nat_sum (sum_localTable_c f)
  · have hc : (⟨7, hi⟩ : Fin 12) = (7 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_7]
    simp_rw [directionColumn, valueAt_column_7]
    exact cast_nat_sum (sum_localTable_f f)
  · have hc : (⟨8, hi⟩ : Fin 12) = (8 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_8]
    simp_rw [directionColumn, valueAt_column_8]
    exact cast_nat_sum (sum_localTable_g f)
  · have hc : (⟨9, hi⟩ : Fin 12) = (9 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_9]
    simp_rw [directionColumn, valueAt_column_9]
    exact cast_nat_sum (sum_localTable_e f)
  · have hc : (⟨10, hi⟩ : Fin 12) = (10 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_10]
    simp_rw [directionColumn, valueAt_column_10]
    exact cast_nat_sum (sum_localTable_h f)
  · have hc : (⟨11, hi⟩ : Fin 12) = (11 : Fin 12) := Fin.ext (by rfl)
    rw [hc, valueAt_rhs_11]
    simp_rw [directionColumn, valueAt_column_11]
    exact cast_nat_sum (sum_localTable_i f)

theorem sum_directionColumn_coordinate
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (coordinate : Fin 12) :
    (∑ ell : V 7, (valueAt (directionColumn f ell) coordinate : Rat)) =
      (valueAt (rhs (spectralProfile f)) coordinate : Rat) := by
  have h := congrArg (fun z : Int => (z : Rat))
    (sum_directionColumn_coordinate_int f hf hnorm hall coordinate)
  push_cast at h
  exact h

section ListPushforward

variable {I A : Type*} [Fintype I] [DecidableEq I] [DecidableEq A]

noncomputable def assignedListIndex
    (values : List A) (g : I -> A) (hmem : ∀ x, g x ∈ values)
    (x : I) : Fin values.length :=
  ⟨values.idxOf (g x), List.idxOf_lt_length_of_mem (hmem x)⟩

omit [Fintype I] [DecidableEq I] in
@[simp] theorem assignedListIndex_get
    (values : List A) (g : I -> A) (hmem : ∀ x, g x ∈ values)
    (x : I) :
    values.get (assignedListIndex values g hmem x) = g x := by
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem x))

noncomputable def fiberMultiplicity
    (values : List A) (g : I -> A) (hmem : ∀ x, g x ∈ values)
    (index : Fin values.length) : Rat :=
  ∑ x ∈ (Finset.univ : Finset I) with
      assignedListIndex values g hmem x = index, 1

omit [DecidableEq I] in
theorem fiberMultiplicity_nonnegative
    (values : List A) (g : I -> A) (hmem : ∀ x, g x ∈ values)
    (index : Fin values.length) :
    0 ≤ fiberMultiplicity values g hmem index := by
  exact Finset.sum_nonneg fun _ _ => by norm_num

omit [DecidableEq I] in
theorem sum_fiberMultiplicity_mul
    (values : List A) (g : I -> A) (hmem : ∀ x, g x ∈ values)
    (phi : A -> Rat) :
    (∑ index : Fin values.length,
        fiberMultiplicity values g hmem index * phi (values.get index)) =
      ∑ x : I, phi (g x) := by
  classical
  calc
    (∑ index : Fin values.length,
        fiberMultiplicity values g hmem index * phi (values.get index)) =
        ∑ index : Fin values.length,
          ∑ x ∈ (Finset.univ : Finset I) with
              assignedListIndex values g hmem x = index,
            phi (g x) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [fiberMultiplicity, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hindex := (Finset.mem_filter.mp hx).2
      rw [show values.get index = g x by
        rw [← hindex]
        exact assignedListIndex_get values g hmem x]
      simp
    _ = ∑ x : I, phi (g x) :=
      Finset.sum_fiberwise (Finset.univ : Finset I)
        (assignedListIndex values g hmem) (fun x => phi (g x))

end ListPushforward

theorem directionColumns_give_nonnegative_rational_solution
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (hmem : ∀ ell : V 7,
      directionColumn f ell ∈ columns (spectralProfile f)) :
    HasNonnegativeRationalSolution (spectralProfile f) := by
  let multiplicity : Fin (columns (spectralProfile f)).length -> Rat :=
    fiberMultiplicity (columns (spectralProfile f))
      (directionColumn f) hmem
  refine ⟨multiplicity, ?_, ?_⟩
  · intro index
    exact fiberMultiplicity_nonnegative
      (columns (spectralProfile f)) (directionColumn f) hmem index
  · intro coordinate
    calc
      (∑ index : Fin (columns (spectralProfile f)).length,
          multiplicity index *
            (valueAt ((columns (spectralProfile f)).get index)
              coordinate : Rat)) =
          ∑ ell : V 7,
            (valueAt (directionColumn f ell) coordinate : Rat) := by
              exact sum_fiberMultiplicity_mul
                (columns (spectralProfile f)) (directionColumn f) hmem
                (fun values => (valueAt values coordinate : Rat))
      _ = (valueAt (rhs (spectralProfile f)) coordinate : Rat) :=
        sum_directionColumn_coordinate f hf hnorm hall coordinate

end LeanCipher.BalancedEight

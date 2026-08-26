import LeanCipher.BalancedEightSlices
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh

/-!
# Normalizing the support XOR

For a nonzero vector `c`, this file constructs an explicit transvection taking
the last standard basis vector to `c`.  The transvection is its own inverse.
Its dual transvection permutes Walsh frequencies, so precomposition preserves
weight, maximum Walsh magnitude, and nonlinearity.
-/

def lastIndex : Fin 8 := Fin.last 7

def lastBasis : V 8 := basisVector lastIndex

@[simp] theorem lastBasis_apply_last : lastBasis lastIndex = 1 := by
  simp [lastBasis, lastIndex]

@[simp] theorem f2Dot_lastBasis_left (x : V 8) :
    f2Dot lastBasis x = x lastIndex := by
  exact f2Dot_basis_left lastIndex x

@[simp] theorem f2Dot_lastBasis_right (x : V 8) :
    f2Dot x lastBasis = x lastIndex := by
  exact f2Dot_basis_right x lastIndex

theorem lastBasis_eq_join : lastBasis = join 0 1 := by
  native_decide

theorem f2Dot_smul_right (a x : V n) (r : ZMod 2) :
    f2Dot a (r • x) = r * f2Dot a x := by
  simp only [f2Dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem f2Dot_smul_left (a x : V n) (r : ZMod 2) :
    f2Dot (r • a) x = r * f2Dot a x := by
  rw [f2Dot_comm, f2Dot_smul_right, f2Dot_comm]

theorem exists_normalizing_covector (c : V 8) (hc : c ≠ 0) :
    ∃ r : V 8, f2Dot r lastBasis = 1 ∧ f2Dot r c = 1 := by
  by_cases hlast : c lastIndex = 0
  · obtain ⟨i, hi⟩ := exists_ne_zero_coordinate hc
    have hiOne : c i = 1 := zmod2_eq_one_of_ne_zero hi
    have hine : i ≠ lastIndex := by
      intro h
      subst i
      exact hi hlast
    have hine' : (7 : Fin 8) ≠ i := by
      simpa [lastIndex] using hine.symm
    have hlast' : c (7 : Fin 8) = 0 := by
      simpa [lastIndex] using hlast
    refine ⟨lastBasis + basisVector i, ?_, ?_⟩
    · rw [f2Dot_add_left]
      simp [lastBasis, basisVector, hine', lastIndex]
    · rw [f2Dot_add_left]
      simp [lastBasis, hlast', hiOne, lastIndex]
  · have hlastOne : c lastIndex = 1 := zmod2_eq_one_of_ne_zero hlast
    refine ⟨lastBasis, ?_, ?_⟩
    · simp [lastBasis]
    · simpa [lastBasis] using hlastOne

noncomputable def normalizingCovector (c : V 8) (hc : c ≠ 0) : V 8 :=
  Classical.choose (exists_normalizing_covector c hc)

theorem normalizingCovector_dot_lastBasis (c : V 8) (hc : c ≠ 0) :
    f2Dot (normalizingCovector c hc) lastBasis = 1 :=
  (Classical.choose_spec (exists_normalizing_covector c hc)).1

theorem normalizingCovector_dot_self (c : V 8) (hc : c ≠ 0) :
    f2Dot (normalizingCovector c hc) c = 1 :=
  (Classical.choose_spec (exists_normalizing_covector c hc)).2

noncomputable def normalizingMap (c : V 8) (hc : c ≠ 0) (x : V 8) : V 8 :=
  x + f2Dot (normalizingCovector c hc) x • (c + lastBasis)

theorem normalizingCovector_dot_displacement (c : V 8) (hc : c ≠ 0) :
    f2Dot (normalizingCovector c hc) (c + lastBasis) = 0 := by
  rw [f2Dot_add_right, normalizingCovector_dot_self,
    normalizingCovector_dot_lastBasis]
  exact CharTwo.add_self_eq_zero 1

theorem normalizingMap_add (c : V 8) (hc : c ≠ 0) (x y : V 8) :
    normalizingMap c hc (x + y) =
      normalizingMap c hc x + normalizingMap c hc y := by
  simp only [normalizingMap, f2Dot_add_right, add_smul]
  module

theorem normalizingMap_smul (c : V 8) (hc : c ≠ 0)
    (r : ZMod 2) (x : V 8) :
    normalizingMap c hc (r • x) = r • normalizingMap c hc x := by
  simp only [normalizingMap, f2Dot_smul_right, smul_add, smul_smul]

noncomputable def normalizingLinear (c : V 8) (hc : c ≠ 0) :
    V 8 →ₗ[ZMod 2] V 8 where
  toFun := normalizingMap c hc
  map_add' := normalizingMap_add c hc
  map_smul' := normalizingMap_smul c hc

theorem normalizingMap_involutive (c : V 8) (hc : c ≠ 0) :
    Function.Involutive (normalizingMap c hc) := by
  intro x
  unfold normalizingMap
  rw [f2Dot_add_right, f2Dot_smul_right,
    normalizingCovector_dot_displacement]
  simp only [mul_zero, add_zero]
  rw [add_assoc, LeanCipher.f2vec_add_self, add_zero]

noncomputable def normalizingEquiv (c : V 8) (hc : c ≠ 0) :
    V 8 ≃ₗ[ZMod 2] V 8 :=
  LinearEquiv.ofInvolutive (normalizingLinear c hc)
    (normalizingMap_involutive c hc)

@[simp] theorem normalizingEquiv_apply (c : V 8) (hc : c ≠ 0) (x : V 8) :
    normalizingEquiv c hc x = normalizingMap c hc x := rfl

theorem normalizingMap_lastBasis (c : V 8) (hc : c ≠ 0) :
    normalizingMap c hc lastBasis = c := by
  rw [normalizingMap, normalizingCovector_dot_lastBasis]
  simp only [one_smul]
  rw [add_comm c lastBasis, ← add_assoc, LeanCipher.f2vec_add_self, zero_add]

theorem normalizingMap_self (c : V 8) (hc : c ≠ 0) :
    normalizingMap c hc c = lastBasis := by
  rw [normalizingMap, normalizingCovector_dot_self]
  simp

noncomputable def normalizingDualMap (c : V 8) (hc : c ≠ 0)
    (a : V 8) : V 8 :=
  a + f2Dot a (c + lastBasis) • normalizingCovector c hc

theorem normalizingDualMap_involutive (c : V 8) (hc : c ≠ 0) :
    Function.Involutive (normalizingDualMap c hc) := by
  intro a
  unfold normalizingDualMap
  rw [f2Dot_add_left, f2Dot_smul_left,
    normalizingCovector_dot_displacement]
  simp only [mul_zero, add_zero]
  rw [add_assoc, LeanCipher.f2vec_add_self, add_zero]

noncomputable def normalizingDualLinear (c : V 8) (hc : c ≠ 0) :
    V 8 →ₗ[ZMod 2] V 8 where
  toFun := normalizingDualMap c hc
  map_add' x y := by
    simp only [normalizingDualMap, f2Dot_add_left, add_smul]
    module
  map_smul' r x := by
    change normalizingDualMap c hc (r • x) =
      r • normalizingDualMap c hc x
    simp only [normalizingDualMap, f2Dot_smul_left, smul_add, smul_smul]

noncomputable def normalizingDualEquiv (c : V 8) (hc : c ≠ 0) :
    V 8 ≃ₗ[ZMod 2] V 8 :=
  LinearEquiv.ofInvolutive (normalizingDualLinear c hc)
    (normalizingDualMap_involutive c hc)

@[simp] theorem normalizingDualEquiv_apply (c : V 8) (hc : c ≠ 0) (a : V 8) :
    normalizingDualEquiv c hc a = normalizingDualMap c hc a := rfl

theorem normalizing_adjoint (c : V 8) (hc : c ≠ 0) (a x : V 8) :
    f2Dot (normalizingDualMap c hc a) x =
      f2Dot a (normalizingMap c hc x) := by
  simp only [normalizingDualMap, normalizingMap, f2Dot_add_left,
    f2Dot_add_right, f2Dot_smul_left, f2Dot_smul_right]
  rw [f2Dot_comm (normalizingCovector c hc) x]
  ring

noncomputable def normalizedFunction
    (f : V 8 -> ZMod 2) (hc : supportXor f ≠ 0) : V 8 -> ZMod 2 :=
  fun x => f (normalizingMap (supportXor f) hc x)

theorem normalizedFunction_weight
    (f : V 8 -> ZMod 2) (hc : supportXor f ≠ 0) :
    weight (normalizedFunction f hc) = weight f := by
  classical
  let e := normalizingEquiv (supportXor f) hc
  have hsum := e.sum_comp (fun x : V 8 => if f x ≠ 0 then 1 else 0)
  have hleft :
      (∑ x : V 8, if normalizedFunction f hc x ≠ 0 then 1 else 0) =
        weight (normalizedFunction f hc) := by
    simpa [weight] using
      Finset.sum_boole (R := Nat)
        (fun x : V 8 => normalizedFunction f hc x ≠ 0) Finset.univ
  have hright :
      (∑ x : V 8, if f x ≠ 0 then 1 else 0) = weight f := by
    simpa [weight] using
      Finset.sum_boole (R := Nat) (fun x : V 8 => f x ≠ 0) Finset.univ
  rw [← hleft, ← hright]
  simpa [normalizedFunction, e] using hsum

theorem normalizedFunction_walsh
    (f : V 8 -> ZMod 2) (hc : supportXor f ≠ 0) (a : V 8) :
    walsh (normalizedFunction f hc) a =
      walsh f (normalizingDualMap (supportXor f) hc a) := by
  classical
  let c := supportXor f
  let e := normalizingEquiv c hc
  let ed := normalizingDualEquiv c hc
  have hsum := e.sum_comp
    (fun x : V 8 => sign (f x + f2Dot (ed a) x))
  unfold walsh normalizedFunction
  calc
    (∑ x : V 8, sign (f (normalizingMap c hc x) + f2Dot a x)) =
        ∑ x : V 8,
          sign (f (e x) + f2Dot (ed a) (e x)) := by
            apply Finset.sum_congr rfl
            intro x _
            simp only [e, ed, normalizingEquiv_apply, normalizingDualEquiv_apply]
            rw [normalizing_adjoint]
            rw [normalizingMap_involutive c hc x]
    _ = ∑ x : V 8, sign (f x + f2Dot (ed a) x) := by
          simpa using hsum

theorem normalizedFunction_maximumWalshMagnitude
    (f : V 8 -> ZMod 2) (hc : supportXor f ≠ 0) :
    maximumWalshMagnitude (normalizedFunction f hc) =
      maximumWalshMagnitude f := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro a _
    rw [normalizedFunction_walsh]
    exact walsh_natAbs_le_maximum f _
  · apply Finset.sup_le
    intro a _
    have h := walsh_natAbs_le_maximum (normalizedFunction f hc)
      (normalizingDualMap (supportXor f) hc a)
    rw [normalizedFunction_walsh,
      normalizingDualMap_involutive (supportXor f) hc a] at h
    exact h

theorem normalizedFunction_nonlinearity
    (f : V 8 -> ZMod 2) (hc : supportXor f ≠ 0) :
    nonlinearity (normalizedFunction f hc) = nonlinearity f := by
  change
    (2 ^ 8 - maximumWalshMagnitude (normalizedFunction f hc)) / 2 =
      (2 ^ 8 - maximumWalshMagnitude f) / 2
  exact congrArg (fun z : Nat => (2 ^ 8 - z) / 2)
    (normalizedFunction_maximumWalshMagnitude f hc)

theorem supportXor_normalizedFunction
    (f : V 8 -> ZMod 2) (hc : supportXor f ≠ 0) :
    supportXor (normalizedFunction f hc) = lastBasis := by
  classical
  let c := supportXor f
  let e := normalizingEquiv c hc
  have hsum := e.sum_comp
    (fun x : V 8 => f x • normalizingMap c hc x)
  have hchange : supportXor (normalizedFunction f hc) =
      ∑ x : V 8, f x • normalizingMap c hc x := by
    unfold supportXor normalizedFunction
    calc
      (∑ x : V 8, f (normalizingMap c hc x) • x) =
          ∑ x : V 8,
            f (e x) • normalizingMap c hc (e x) := by
              apply Finset.sum_congr rfl
              intro x _
              simp only [e, normalizingEquiv_apply]
              rw [normalizingMap_involutive c hc x]
      _ = ∑ x : V 8, f x • normalizingMap c hc x := by
            simpa using hsum
  rw [hchange]
  change (∑ x : V 8, f x • normalizingLinear c hc x) = lastBasis
  calc
    (∑ x : V 8, f x • normalizingLinear c hc x) =
        ∑ x : V 8, normalizingLinear c hc (f x • x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [map_smul]
    _ = normalizingLinear c hc (∑ x : V 8, f x • x) := by
          rw [map_sum]
    _ = lastBasis := normalizingMap_self c hc

end LeanCipher.BalancedEight

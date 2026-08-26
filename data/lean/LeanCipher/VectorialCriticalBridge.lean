import LeanCipher.VectorialBent
import LeanCipher.VectorialCoordinates
import LeanCipher.VectorialCritical

open scoped BigOperators

namespace LeanCipher.VectorialCriticalBridge

open LeanCipher.BooleanWalsh
open LeanCipher.VectorialBent
open LeanCipher.VectorialCoordinates
open LeanCipher.VectorialCritical

noncomputable section

/-!
Choose coordinates on the even-component hyperplane and one complementary
component.  This turns an arbitrary critical-output function into the
`(G,h)` presentation used by the congruence argument, without treating an
output change of basis as an implicit paper-level step.
-/

theorem exists_critical_coordinates
    {k : Nat} (F : V (2 * k) -> V (k + 1))
    (hs : Not (outputSum F = 0))
    (hKernelBent : forall v, Not (v = 0) ->
      f2Dot v (outputSum F) = 0 -> IsBent (component F v))
    (hCeiling : forall v, Not (v = 0) -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    exists G : V (2 * k) -> V k, exists h : V (2 * k) -> ZMod 2,
      (forall u, Not (u = 0) -> forall a,
        |walsh (component G u) a| = (2 : Int) ^ k) /\
      (forall u, Odd (weight (cosetFunction G h u))) /\
      (forall u a,
        |walsh (cosetFunction G h u) a| <= (2 : Int) ^ k + 2) := by
  let K := (dotRight (outputSum F)).ker
  have hKdim : Module.finrank (ZMod 2) K = k := by
    dsimp [K]
    rw [dotRight_ker_finrank hs]
    omega
  let b : Module.Basis (Fin k) (ZMod 2) K :=
    Module.finBasisOfFinrankEq (ZMod 2) K hKdim
  let G : V (2 * k) -> V k := componentCoordinateMap K F b
  obtain ⟨t, ht⟩ := dotRight_surjective hs (1 : ZMod 2)
  have ht' : f2Dot t (outputSum F) = 1 := ht
  let h : V (2 * k) -> ZMod 2 := component F t
  refine ⟨G, h, ?_, ?_, ?_⟩
  · intro u hu a
    rw [component_componentCoordinateMap]
    apply hKernelBent
    · intro he
      exact basisCoordinates_ne_zero K b hu (Subtype.ext he)
    · exact (b.equivFun.symm u).property
  · intro u
    let e : V (k + 1) := (b.equivFun.symm u).1
    have heOrth : f2Dot e (outputSum F) = 0 :=
      (b.equivFun.symm u).property
    have hindex : f2Dot (t + e) (outputSum F) = 1 := by
      rw [f2Dot_add_left, ht', heOrth, add_zero]
    have hcast : (weight (component F (t + e)) : ZMod 2) = 1 := by
      rw [component_weight_cast, hindex]
    have hoddIndex : Odd (weight (component F (t + e))) :=
      ZMod.natCast_eq_one_iff_odd.mp hcast
    convert hoddIndex using 1
    apply congrArg weight
    funext x
    simp only [cosetFunction, h, G]
    rw [component_componentCoordinateMap]
    exact congrFun (component_add F t e).symm x
  · intro u a
    let e : V (k + 1) := (b.equivFun.symm u).1
    have heOrth : f2Dot e (outputSum F) = 0 :=
      (b.equivFun.symm u).property
    have hindex : f2Dot (t + e) (outputSum F) = 1 := by
      rw [f2Dot_add_left, ht', heOrth, add_zero]
    have hne : Not (t + e = 0) := by
      intro hz
      rw [hz, f2Dot_zero_left] at hindex
      exact zero_ne_one hindex
    have heq : cosetFunction G h u = component F (t + e) := by
      funext x
      simp only [cosetFunction, h, G]
      rw [component_componentCoordinateMap]
      exact congrFun (component_add F t e).symm x
    rw [heq]
    exact hCeiling (t + e) hne a

end

end LeanCipher.VectorialCriticalBridge

import LeanCipher.BooleanWalsh
import Mathlib

open scoped BigOperators

namespace LeanCipher.VectorialCoordinates

open LeanCipher.BooleanWalsh

variable (K : Submodule (ZMod 2) (V m))

noncomputable def componentCoordinateMap
    (F : V n -> V m) (b : Module.Basis (Fin r) (ZMod 2) K) : V n -> V r :=
  fun x i => component F (b i).1 x

theorem f2Dot_sum_smul
    (u : V r) (b : Module.Basis (Fin r) (ZMod 2) K) (y : V m) :
    f2Dot (∑ i, u i • (b i).1) y = ∑ i, u i * f2Dot (b i).1 y := by
  simp only [f2Dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem component_componentCoordinateMap
    (F : V n -> V m) (b : Module.Basis (Fin r) (ZMod 2) K) (u : V r) :
    component (componentCoordinateMap K F b) u =
      component F ((b.equivFun.symm u).1) := by
  funext x
  rw [component_apply, component_apply]
  change (∑ i, u i * f2Dot (b i).1 (F x)) =
    f2Dot (b.equivFun.symm u).1 (F x)
  rw [Module.Basis.equivFun_symm_apply]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  rw [f2Dot_sum_smul K]

theorem basisCoordinates_ne_zero
    (b : Module.Basis (Fin r) (ZMod 2) K) {u : V r} (hu : Not (u = 0)) :
    Not (b.equivFun.symm u = 0) := by
  exact fun h => hu (b.equivFun.symm.injective (h.trans (map_zero _).symm))

end LeanCipher.VectorialCoordinates

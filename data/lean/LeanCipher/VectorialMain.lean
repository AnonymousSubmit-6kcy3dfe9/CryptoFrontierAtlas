import LeanCipher.VectorialBent
import LeanCipher.VectorialCoordinates
import LeanCipher.VectorialCriticalBridge
import LeanCipher.VectorialHyperplane
import LeanCipher.VectorialNonlinearity

open scoped BigOperators

namespace LeanCipher.VectorialMain

open LeanCipher.BooleanWalsh
open LeanCipher.VectorialBent
open LeanCipher.VectorialCoordinates
open LeanCipher.VectorialCritical
open LeanCipher.VectorialCriticalBridge
open LeanCipher.VectorialHyperplane

noncomputable section

theorem ceiling_forces_critical_coordinates
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m)
    (hCeiling : forall v, Not (v = 0) -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    exists G : V (2 * k) -> V k, exists h : V (2 * k) -> ZMod 2,
      (forall u, Not (u = 0) -> forall a,
        |walsh (component G u) a| = (2 : Int) ^ k) /\
      (forall u, Odd (weight (cosetFunction G h u))) /\
      (forall u a,
        |walsh (cosetFunction G h u) a| <= (2 : Int) ^ k + 2) := by
  obtain ⟨hs, _hKdim, _hKernelBent, hDimension⟩ :=
    bent_hyperplane_of_spectral_ceiling hk hm F hCeiling
  have hmCritical : m = k + 1 := by omega
  subst m
  apply exists_critical_coordinates F hs
  · intro v hv hOrthogonal
    exact component_bent_of_orthogonal_output_sum (by omega) F hCeiling hv hOrthogonal
  · exact hCeiling

theorem spectral_ceiling_contradiction
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m)
    (hCeiling : forall v, Not (v = 0) -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    False := by
  obtain ⟨G, h, hBent, hOdd, hCosetCeiling⟩ :=
    ceiling_forces_critical_coordinates hk hm F hCeiling
  exact critical_coset_contradiction k hk G h hBent hOdd hCosetCeiling

theorem exists_large_component_walsh
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m) :
    exists v : V m, Not (v = 0) ∧ exists a : V (2 * k),
      ((2 ^ k + 4 : Nat) : Int) <= |walsh (component F v) a| := by
  by_contra hNoWitness
  push Not at hNoWitness
  have hCeiling : forall v, Not (v = 0) -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2 := by
    intro v hv a
    have hlt : |walsh (component F v) a| < ((2 ^ k + 4 : Nat) : Int) :=
      hNoWitness v hv a
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using
      LeanCipher.VectorialNonlinearity.walsh_abs_le_next_even
        (component F v) a (by omega : 1 <= k) hlt
  exact spectral_ceiling_contradiction hk hm F hCeiling

theorem vectorial_nonlinearity_bound
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m) :
    LeanCipher.VectorialNonlinearity.nonlinearity F <=
      2 ^ (2 * k - 1) - 2 ^ (k - 1) - 2 := by
  obtain ⟨v, hv, a, hlarge⟩ := exists_large_component_walsh hk hm F
  exact LeanCipher.VectorialNonlinearity.nonlinearity_le_main_bound_of_intAbs_witness
    F (by omega) v a hv hlarge

end

end LeanCipher.VectorialMain

import LeanCipher.BooleanWalsh
import LeanCipher.VectorialBent

open scoped BigOperators

namespace LeanCipher.VectorialHyperplane

open BooleanWalsh

theorem four_dvd_pow_two (k : Nat) (hk : 2 <= k) :
    (4 : Int) ∣ (2 : Int) ^ k := by
  refine ⟨(2 : Int) ^ (k - 2), ?_⟩
  rw [show k = 2 + (k - 2) by omega, pow_add]
  norm_num

theorem abs_walsh_le_bent_level_of_even_weight
    {k : Nat} (hk : 2 <= k) (f : V (2 * k) -> ZMod 2)
    (hf : Even (weight f))
    (hBound : forall a, |walsh f a| <= (2 : Int) ^ k + 2) :
    forall a, |walsh f a| <= (2 : Int) ^ k := by
  intro a
  obtain ⟨z, hz⟩ := four_dvd_walsh_of_weight_even f a (by omega) hf
  obtain ⟨r, hr⟩ := four_dvd_pow_two k hk
  have h := hBound a
  rw [hz, hr, abs_mul] at h ⊢
  norm_num at h ⊢
  omega

theorem even_weight_bent_of_spectral_ceiling
    {k : Nat} (hk : 2 <= k) (f : V (2 * k) -> ZMod 2)
    (hf : Even (weight f))
    (hBound : forall a, |walsh f a| <= (2 : Int) ^ k + 2) :
    forall a, |walsh f a| = (2 : Int) ^ k := by
  have hAbsBound := abs_walsh_le_bent_level_of_even_weight hk f hf hBound
  have hSquareBound (a : V (2 * k)) :
      walsh f a ^ 2 <= ((2 : Int) ^ k) ^ 2 := by
    have habs := hAbsBound a
    have hnonneg : (0 : Int) <= (2 : Int) ^ k := by positivity
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hnonneg] using habs)
  have hSumEquality :
      (Finset.univ.sum fun a : V (2 * k) => walsh f a ^ 2) =
        Finset.univ.sum (fun _a : V (2 * k) => ((2 : Int) ^ k) ^ 2) := by
    rw [walsh_parseval]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [f2Vec_card]
    push_cast
    rw [show 2 * k = k + k by omega, pow_add]
    ring
  have hAllSquares : forall a : V (2 * k),
      walsh f a ^ 2 = ((2 : Int) ^ k) ^ 2 := by
    have hPointwise :=
      (Finset.sum_eq_sum_iff_of_le
        (s := (Finset.univ : Finset (V (2 * k))))
        (f := fun a => walsh f a ^ 2)
        (g := fun _a => ((2 : Int) ^ k) ^ 2)
        (fun a _ => hSquareBound a)).mp hSumEquality
    intro a
    exact hPointwise a (Finset.mem_univ a)
  intro a
  have hnonneg : (0 : Int) <= (2 : Int) ^ k := by positivity
  have habsnonneg := abs_nonneg (walsh f a)
  nlinarith [sq_abs (walsh f a), hAllSquares a]

theorem component_bent_of_orthogonal_output_sum
    {k m : Nat} (hk : 2 <= k) (F : V (2 * k) -> V m)
    (hBound : forall v, v ≠ 0 -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2)
    {v : V m} (hv : v ≠ 0)
    (hOrthogonal : f2Dot v (VectorialBent.outputSum F) = 0) :
    forall a, |walsh (component F v) a| = (2 : Int) ^ k := by
  apply even_weight_bent_of_spectral_ceiling hk
  · exact (VectorialBent.component_weight_even_iff F v).mpr hOrthogonal
  · exact hBound v hv

def evenComponentKernel (F : V n -> V m) : Submodule (ZMod 2) (V m) :=
  (VectorialBent.dotRight (VectorialBent.outputSum F)).ker

theorem mem_evenComponentKernel_iff (F : V n -> V m) (v : V m) :
    v ∈ evenComponentKernel F ↔
      f2Dot v (VectorialBent.outputSum F) = 0 := by
  rfl

theorem component_weight_even_iff_mem_kernel (F : V n -> V m) (v : V m) :
    Even (weight (component F v)) ↔ v ∈ evenComponentKernel F := by
  rw [VectorialBent.component_weight_even_iff, mem_evenComponentKernel_iff]

theorem nonzero_kernel_component_isBent
    {k m : Nat} (hk : 2 <= k) (F : V (2 * k) -> V m)
    (hBound : forall v, v ≠ 0 -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2)
    (v : evenComponentKernel F) (hv : v ≠ 0) :
    VectorialBent.IsBent (component F (v : V m)) := by
  apply component_bent_of_orthogonal_output_sum hk F hBound
  · intro hvCoe
    apply hv
    exact Subtype.ext hvCoe
  · exact (mem_evenComponentKernel_iff F v).mp v.property

theorem basisVector_sum (b : V r) :
    (∑ i, b i • basisVector i) = b := by
  classical
  funext j
  simp [basisVector]

theorem linearMap_eq_dot_basis_values
    (L : V r →ₗ[ZMod 2] ZMod 2) (b : V r) :
    f2Dot b (fun i => L (basisVector i)) = L b := by
  classical
  calc
    f2Dot b (fun i => L (basisVector i)) =
        ∑ i, b i * L (basisVector i) := rfl
    _ = ∑ i, L (b i • basisVector i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = L (∑ i, b i • basisVector i) := by rw [map_sum]
    _ = L b := by rw [basisVector_sum]

noncomputable def subspaceOutputEquiv (S : Submodule (ZMod 2) (V m)) :
    V (Module.finrank (ZMod 2) S) ≃ₗ[ZMod 2] S :=
  LinearEquiv.ofFinrankEq _ _ (by simp)

noncomputable def restrictOutputToSubspace
    (F : V n -> V m) (S : Submodule (ZMod 2) (V m)) :
    V n -> V (Module.finrank (ZMod 2) S) :=
  fun x i => f2Dot ((subspaceOutputEquiv S (basisVector i) : S) : V m) (F x)

theorem component_restrictOutputToSubspace
    (F : V n -> V m) (S : Submodule (ZMod 2) (V m))
    (b : V (Module.finrank (ZMod 2) S)) :
    component (restrictOutputToSubspace F S) b =
      component F ((subspaceOutputEquiv S b : S) : V m) := by
  funext x
  let L : V (Module.finrank (ZMod 2) S) →ₗ[ZMod 2] ZMod 2 :=
    ((VectorialBent.dotRight (F x)).comp (Submodule.subtype S)).comp
      (subspaceOutputEquiv S).toLinearMap
  change f2Dot b (fun i => L (basisVector i)) = L b
  exact linearMap_eq_dot_basis_values L b

theorem restrictOutputToSubspace_isVectorialBent
    {k m : Nat} (F : V (2 * k) -> V m) (S : Submodule (ZMod 2) (V m))
    (hBent : forall v : S, v ≠ 0 ->
      VectorialBent.IsBent (component F (v : V m))) :
    VectorialBent.IsVectorialBent (restrictOutputToSubspace F S) := by
  intro b hb
  rw [component_restrictOutputToSubspace]
  apply hBent (subspaceOutputEquiv S b)
  simpa using (subspaceOutputEquiv S).injective.ne hb

theorem bent_subspace_finrank_le
    {k m : Nat} (hk : 0 < k) (F : V (2 * k) -> V m)
    (S : Submodule (ZMod 2) (V m))
    (hBent : forall v : S, v ≠ 0 ->
      VectorialBent.IsBent (component F (v : V m))) :
    Module.finrank (ZMod 2) S <= k := by
  exact VectorialBent.nyberg_bound hk
    (restrictOutputToSubspace_isVectorialBent F S hBent)

theorem outputSum_ne_zero_of_spectral_ceiling
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m)
    (hBound : forall v, v ≠ 0 -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    VectorialBent.outputSum F ≠ 0 := by
  intro hSum
  have hVectorialBent : VectorialBent.IsVectorialBent F := by
    intro v hv
    apply component_bent_of_orthogonal_output_sum (by omega) F hBound hv
    rw [hSum]
    exact f2Dot_zero_right v
  have hNyberg := VectorialBent.nyberg_bound (by omega) hVectorialBent
  omega

theorem evenComponentKernel_finrank
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m)
    (hBound : forall v, v ≠ 0 -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    Module.finrank (ZMod 2) (evenComponentKernel F) = m - 1 := by
  exact VectorialBent.dotRight_ker_finrank
    (outputSum_ne_zero_of_spectral_ceiling hk hm F hBound)

theorem evenComponentKernel_finrank_le
    {k m : Nat} (hk : 3 <= k) (F : V (2 * k) -> V m)
    (hBound : forall v, v ≠ 0 -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    Module.finrank (ZMod 2) (evenComponentKernel F) <= k := by
  apply bent_subspace_finrank_le (by omega) F (evenComponentKernel F)
  exact nonzero_kernel_component_isBent (by omega) F hBound

theorem bent_hyperplane_of_spectral_ceiling
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m)
    (hBound : forall v, v ≠ 0 -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    VectorialBent.outputSum F ≠ 0 ∧
      Module.finrank (ZMod 2) (evenComponentKernel F) = m - 1 ∧
      (forall v : evenComponentKernel F, v ≠ 0 ->
        VectorialBent.IsBent (component F (v : V m))) ∧
      m - 1 <= k := by
  refine ⟨outputSum_ne_zero_of_spectral_ceiling hk hm F hBound,
    evenComponentKernel_finrank hk hm F hBound, ?_, ?_⟩
  · exact nonzero_kernel_component_isBent (by omega) F hBound
  · exact (evenComponentKernel_finrank hk hm F hBound) ▸
      evenComponentKernel_finrank_le hk F hBound

theorem spectral_ceiling_implies_m_le_k_add_one
    {k m : Nat} (hk : 3 <= k) (hm : k < m)
    (F : V (2 * k) -> V m)
    (hBound : forall v, v ≠ 0 -> forall a,
      |walsh (component F v) a| <= (2 : Int) ^ k + 2) :
    m <= k + 1 := by
  have h := (bent_hyperplane_of_spectral_ceiling hk hm F hBound).2.2.2
  omega

end LeanCipher.VectorialHyperplane

import LeanCipher.VectorialMain

namespace CryptoFrontierAtlas.VectorialNonlinearityComplete

open LeanCipher.BooleanWalsh

/-!
Complete formalization of the uniform vectorial-nonlinearity bound in the
submission.  The implementation proves the slightly stronger spectral result
using only `k < m`; this public theorem retains the paper's range `m < 2*k`.
-/

theorem vectorial_nonlinearity_is_minimum_component
    {n m : Nat} (hm : 0 < m) (F : V n -> V m) :
    LeanCipher.VectorialNonlinearity.nonlinearity F =
      LeanCipher.VectorialNonlinearity.minComponentNonlinearity F hm :=
  LeanCipher.VectorialNonlinearity.nonlinearity_eq_scalar_component_min F hm

theorem vectorial_nonlinearity_min_component_spec
    {n m : Nat} (hm : 0 < m) (F : V n -> V m) :
    ∃ v : V m, v ≠ 0 ∧
      LeanCipher.BooleanNonlinearity.nonlinearity (component F v) =
        LeanCipher.VectorialNonlinearity.nonlinearity F := by
  obtain ⟨v, hv, hmin⟩ :=
    LeanCipher.VectorialNonlinearity.exists_minComponentNonlinearity F hm
  refine ⟨v, hv, ?_⟩
  rw [hmin, ← vectorial_nonlinearity_is_minimum_component hm F]

theorem uniform_walsh_bound_beyond_nyberg
    (k m : Nat) (hk : 3 <= k) (hmLower : k < m) (_hmUpper : m < 2 * k)
    (F : V (2 * k) -> V m) :
    exists v : V m, Not (v = 0) ∧ exists a : V (2 * k),
      ((2 ^ k + 4 : Nat) : Int) <= |walsh (component F v) a| := by
  exact LeanCipher.VectorialMain.exists_large_component_walsh hk hmLower F

theorem uniform_vectorial_nonlinearity_bound
    (k m : Nat) (hk : 3 <= k) (hmLower : k < m) (_hmUpper : m < 2 * k)
    (F : V (2 * k) -> V m) :
    LeanCipher.VectorialNonlinearity.nonlinearity F <=
      2 ^ (2 * k - 1) - 2 ^ (k - 1) - 2 := by
  exact LeanCipher.VectorialMain.vectorial_nonlinearity_bound hk hmLower F

end CryptoFrontierAtlas.VectorialNonlinearityComplete

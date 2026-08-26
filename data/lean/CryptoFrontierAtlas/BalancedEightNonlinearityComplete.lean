import LeanCipher.BalancedEightComplete

namespace CryptoFrontierAtlas.BalancedEightNonlinearityComplete

open LeanCipher.BooleanWalsh

/-!
# Sharp balanced eight-variable nonlinearity bound

This module exposes the complete formalization of the paper's eight-variable
result. The proof rules out nonlinearity `118` for every balanced Boolean
function and includes an explicit balanced function attaining `116`.

The finite local enumerations, integer Farkas certificates, finite parity
checks, and explicit witness are replayed with `native_decide`; the surrounding
reductions and soundness bridges are checked by Lean.
-/

theorem balanced_eight_nonlinearity_is_affine_distance
    (f : V 8 -> ZMod 2) :
    LeanCipher.BalancedEight.nonlinearity f =
      LeanCipher.BooleanNonlinearity.distanceToAffine f :=
  LeanCipher.BooleanNonlinearity.nonlinearity_eq_minimum_affine_hamming_distance f

theorem balanced_eight_nonlinearity_le_116
    (f : V 8 -> ZMod 2) (hf : weight f = 128) :
    LeanCipher.BalancedEight.nonlinearity f <= 116 :=
  LeanCipher.BalancedEight.balanced_eight_nonlinearity_le_116 f hf

theorem balanced_eight_bound_is_sharp :
    (forall f : V 8 -> ZMod 2, weight f = 128 ->
      LeanCipher.BalancedEight.nonlinearity f <= 116) /\
      exists f : V 8 -> ZMod 2,
        weight f = 128 /\ LeanCipher.BalancedEight.nonlinearity f = 116 :=
  LeanCipher.BalancedEight.balanced_eight_bound_is_sharp

end CryptoFrontierAtlas.BalancedEightNonlinearityComplete

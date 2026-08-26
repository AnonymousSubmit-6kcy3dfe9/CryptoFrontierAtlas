import LeanCipher.BalancedEightCore

open scoped BigOperators

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh

/-!
# An explicit balanced eight-variable function of nonlinearity 116

The truth table is encoded least-significant-bit first: coordinate `i` of an
input has place value `2^i`, and the resulting input index selects a bit of
the 256-bit word below.  The function lives directly in the public
`V 8 -> ZMod 2` API used by the rest of the formalization.
-/

def witnessWord : Nat :=
  0xee47b888c64d30227cbe575846c1fe42de03879685c95ec9a71be53a54f24976

def witnessInputIndex (x : V 8) : Nat :=
  ∑ i : Fin 8, (x i).val * 2 ^ (i : Nat)

def witnessFunction (x : V 8) : ZMod 2 :=
  if Nat.testBit witnessWord (witnessInputIndex x) then 1 else 0

theorem witness_weight : weight witnessFunction = 128 := by
  native_decide

theorem witness_maximumWalshMagnitude :
    maximumWalshMagnitude witnessFunction = 24 := by
  native_decide

theorem witness_nonlinearity : nonlinearity witnessFunction = 116 := by
  show LeanCipher.BooleanNonlinearity.nonlinearity witnessFunction = 116
  rw [LeanCipher.BooleanNonlinearity.nonlinearity]
  rw [show LeanCipher.BooleanNonlinearity.maximumWalshMagnitude witnessFunction = 24
      from witness_maximumWalshMagnitude]
  norm_num

theorem witness_parameters :
    weight witnessFunction = 128 ∧
      maximumWalshMagnitude witnessFunction = 24 ∧
      nonlinearity witnessFunction = 116 :=
  ⟨witness_weight, witness_maximumWalshMagnitude, witness_nonlinearity⟩

end LeanCipher.BalancedEight

import LeanCipher.BalancedEightSemantic
import LeanCipher.BalancedEightFunctionBridge
import LeanCipher.BalancedEightCommonQuadratic
import LeanCipher.BalancedEightTerminal
import LeanCipher.BalancedEightWitness

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh

/-!
# Sharp nonlinearity bound for balanced eight-variable Boolean functions

The normalized contradiction combines the complete local enumeration, the
global Farkas certificates, the common quadratic first bit, and the terminal
rank certificates.  The final theorem transports the contradiction back
through the support-XOR normalization.
-/

theorem normalized_counterexample_impossible
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : ∀ a : V 8, (walsh f a).natAbs ≤ 20)
    (hexists : ∃ a : V 8, (walsh f a).natAbs = 20) :
    False := by
  have hsemantic :=
    LeanCipher.BalancedEightSemantic.localTable_semantic_conditions
      f hf hnorm hall
  have hsurvivor := spectralProfile_mem_declaredSurvivors_of_semantic
    f hf hnorm hall hexists hsemantic
  obtain ⟨R, hR⟩ :=
    LeanCipher.BalancedEightCommonQuadratic.exists_common_quadratic
      f hf hnorm hall
  exact LeanCipher.BalancedEightTerminal.declared_survivor_terminal_contradiction
    f hf hnorm hall R hR hsurvivor

theorem balanced_eight_nonlinearity_le_116
    (f : V 8 -> ZMod 2) (hf : weight f = 128) :
    nonlinearity f ≤ 116 := by
  by_contra hbound
  have hNL : 116 < nonlinearity f := Nat.lt_of_not_ge hbound
  obtain ⟨hall, _hexists⟩ := hypothetical_spectrum_bounds f hf hNL
  have hsupport : supportXor f ≠ 0 :=
    supportXor_ne_zero_of_hypothetical f hf hall
  let g : V 8 -> ZMod 2 := normalizedFunction f hsupport
  have hgf : weight g = 128 := by
    rw [show g = normalizedFunction f hsupport by rfl,
      normalizedFunction_weight, hf]
  have hgnorm : supportXor g = lastBasis := by
    exact supportXor_normalizedFunction f hsupport
  have hgNL : 116 < nonlinearity g := by
    rw [show g = normalizedFunction f hsupport by rfl,
      normalizedFunction_nonlinearity]
    exact hNL
  obtain ⟨hgall, hgexists⟩ := hypothetical_spectrum_bounds g hgf hgNL
  exact normalized_counterexample_impossible
    g hgf hgnorm hgall hgexists

theorem balanced_eight_bound_is_sharp :
    (∀ f : V 8 -> ZMod 2, weight f = 128 -> nonlinearity f ≤ 116) ∧
      ∃ f : V 8 -> ZMod 2,
        weight f = 128 ∧ nonlinearity f = 116 := by
  constructor
  · intro f hf
    exact balanced_eight_nonlinearity_le_116 f hf
  · exact ⟨witnessFunction, witness_weight, witness_nonlinearity⟩

end LeanCipher.BalancedEight

import LeanCipher.TuDengZModBridge
import LeanCipher.TuDengPartition

namespace LeanCipher.TuDengComplete

open LeanCipher
open LeanCipher.TuDengBooleanBridge
open LeanCipher.TuDengCube
open LeanCipher.TuDengCyclic
open LeanCipher.TuDengPartition
open LeanCipher.TuDengZModBridge

variable {k : Nat} [NeZero k]

/-! The two presentations of the Boolean cube used by the arithmetic bridge
and by the pivotal argument are definitionally inverse up to extensionality. -/

noncomputable def inputSetEquiv (k : Nat) [NeZero k] :
    (ZMod k -> Bool) ≃ Finset (ZMod k) where
  toFun := setOfInput
  invFun := inputOfSet
  left_inv := inputOfSet_setOfInput
  right_inv := setOfInput_inputOfSet

theorem cyclicBadFamily_card_eq_propBadFamily_card (k t : Nat) [NeZero k] :
    (cyclicBadFamily k t).card =
      (propBadFamily (zmodTargetWord k t)).card := by
  classical
  apply Finset.card_equiv (inputSetEquiv k)
  intro x
  simp [inputSetEquiv, cyclicBadFamily, propBadFamily]

/-! A nonconstant target makes the bottom and top vertices genuine opposite
endpoints of the increasing bad family.  The strict weight inequality is the
convenient, representation-independent form of nonconstancy here. -/

theorem selectedCarry_empty_eq_false
    (d : InputWord k) (hdlt : inputWeight d < k) :
    selectedCarry (inputOfSet (k := k) ∅) d = fun _ => False := by
  have hfalse : CarryCompatible (inputOfSet (k := k) ∅) d (fun _ => False) := by
    intro j
    cases d j <;> simp [gate, inputOfSet]
  obtain ⟨j, hj⟩ : ∃ j, d j = false := by
    by_contra h
    have hall : ∀ j, d j = true := by
      intro j
      cases hd : d j with
      | false => exact (h ⟨j, hd⟩).elim
      | true => rfl
    have hweight : inputWeight d = k := by
      simp [inputWeight, hall]
    omega
  have hselected := selectedCarry_compatible (inputOfSet (k := k) ∅) d
  have hnext : ¬ selectedCarry (inputOfSet (k := k) ∅) d (j + 1) := by
    rw [hselected j]
    simp [gate, inputOfSet, hj]
  funext q
  apply propext
  exact compatible_eq_everywhere_of_eq_at hfalse hselected
    (iff_of_false hnext (by simp)) q

theorem empty_not_mem_propBadFamily
    (d : InputWord k) (hdlt : inputWeight d < k) :
    (∅ : Finset (ZMod k)) ∉ propBadFamily d := by
  rw [mem_propBadFamily, selectedCarry_empty_eq_false d hdlt]
  simp [weight, carrySet]

theorem selectedCarry_univ_eq_true (d : InputWord k) :
    selectedCarry (inputOfSet (k := k) Finset.univ) d = fun _ => True := by
  have htrue : CarryCompatible
      (inputOfSet (k := k) Finset.univ) d (fun _ => True) := by
    intro j
    cases d j <;> simp [gate, inputOfSet]
  have hle := compatible_le_selected htrue
  funext j
  apply propext
  exact iff_true_intro (hle j trivial)

theorem univ_mem_propBadFamily
    (d : InputWord k) (hdlt : inputWeight d < k) :
    (Finset.univ : Finset (ZMod k)) ∈ propBadFamily d := by
  rw [mem_propBadFamily, selectedCarry_univ_eq_true]
  simpa [weight, carrySet] using hdlt

theorem zmodTarget_inputWeight_pos
    {k t : Nat} [NeZero k] (hk : 1 ≤ k) (htPos : 1 ≤ t)
    (ht : t ≤ 2 ^ k - 2) :
    0 < inputWeight (zmodTargetWord k t) := by
  have hpow : 2 ≤ 2 ^ k := by
    have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by decide)
    omega
  rw [show zmodTargetWord k t = finZModWordEquiv k (targetWord k t) from rfl,
    inputWeight_reindex, wordWeight_targetWord]
  exact binaryWeightUpTo_pos_of_pos (by omega) (by omega)

theorem zmodTarget_inputWeight_lt
    {k t : Nat} [NeZero k] (hk : 1 ≤ k)
    (ht : t ≤ 2 ^ k - 2) :
    inputWeight (zmodTargetWord k t) < k := by
  have hpow : 2 ≤ 2 ^ k := by
    have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hcompPos : 0 < binaryWeightUpTo k (2 ^ k - 1 - t) := by
    exact binaryWeightUpTo_pos_of_pos (by omega) (by omega)
  have hcomplement := binaryWeightUpTo_complement
    (k := k) (n := t) (by omega)
  rw [show zmodTargetWord k t = finZModWordEquiv k (targetWord k t) from rfl,
    inputWeight_reindex, wordWeight_targetWord]
  omega

theorem false_not_mem_cyclicBadFamily
    {k t : Nat} [NeZero k] (hk : 1 ≤ k)
    (ht : t ≤ 2 ^ k - 2) :
    (fun _ : ZMod k => false) ∉ cyclicBadFamily k t := by
  classical
  have hdlt := zmodTarget_inputWeight_lt (k := k) (t := t) hk ht
  have hinput : (fun _ : ZMod k => false) = inputOfSet (k := k) ∅ := by
    funext j
    simp [inputOfSet]
  rw [cyclicBadFamily]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hinput, selectedCarry_empty_eq_false (zmodTargetWord k t) hdlt]
  simp [weight, carrySet]

theorem true_mem_cyclicBadFamily
    {k t : Nat} [NeZero k] (hk : 1 ≤ k)
    (ht : t ≤ 2 ^ k - 2) :
    (fun _ : ZMod k => true) ∈ cyclicBadFamily k t := by
  classical
  have hdlt := zmodTarget_inputWeight_lt (k := k) (t := t) hk ht
  have hinput : (fun _ : ZMod k => true) =
      inputOfSet (k := k) Finset.univ := by
    funext j
    simp [inputOfSet]
  rw [cyclicBadFamily]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hinput, selectedCarry_univ_eq_true]
  simpa [weight, carrySet] using hdlt

/-! P11 now closes without a problem-specific analytic argument: the
partition theorem supplies the profile comparison, and the generic cube
calculus converts it to the half-cube cardinality bound. -/

theorem propBadFamily_card_le_half
    (d : InputWord k) (hdpos : 0 < inputWeight d)
    (hdlt : inputWeight d < k) :
    (propBadFamily d).card ≤ 2 ^ (k - 1) := by
  have hbound := card_le_half_cube_of_profile_comparison
    (propBadFamily d) (propBadFamily_increasing d)
    (empty_not_mem_propBadFamily d hdlt)
    (univ_mem_propBadFamily d hdlt)
    (fun hp => propBadFamily_profile_comparison hdpos hp)
  simpa using hbound

theorem tu_deng_conjecture_root
    {k t : Nat}
    (hk : 2 ≤ k)
    (htPos : 1 ≤ t)
    (htUpper : t ≤ 2 ^ k - 2) :
    tuDengCount k t ≤ 2 ^ (k - 1) := by
  letI : NeZero k := ⟨by omega⟩
  let d := zmodTargetWord k t
  have hdpos : 0 < inputWeight d := by
    exact zmodTarget_inputWeight_pos (k := k) (t := t) (by omega) htPos htUpper
  have hdlt : inputWeight d < k := by
    exact zmodTarget_inputWeight_lt (k := k) (t := t) (by omega) htUpper
  calc
    tuDengCount k t = (cyclicBadFamily k t).card :=
      tuDengCount_eq_cyclicBadFamily_card hk htPos htUpper
    _ = (propBadFamily d).card := by
      exact cyclicBadFamily_card_eq_propBadFamily_card k t
    _ ≤ 2 ^ (k - 1) := propBadFamily_card_le_half d hdpos hdlt

theorem tu_deng_conjecture : TuDengConjecture := by
  intro k t hk htPos htUpper
  exact tu_deng_conjecture_root hk htPos htUpper

end LeanCipher.TuDengComplete

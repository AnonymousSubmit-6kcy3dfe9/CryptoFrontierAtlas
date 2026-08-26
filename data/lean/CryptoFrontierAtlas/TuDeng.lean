import Mathlib

namespace CryptoFrontierAtlas

/-!
  A native-replayable finite check for the Tu--Deng count.

  The paper's pivotal-integral argument is an infinite parameter proof and is
  deliberately not hidden behind an axiom here.  This file formalizes the
  exact source count, its circular counterpart, and exhaustively checks the
  stated inequality for every word length through eight bits.  These closed
  finite propositions use native_decide, so their trust boundary includes
  Lean's compiled evaluator in addition to Lean/mathlib.  They are useful as
  regression certificates for the definitions used by the paper.
-/

def bit (n i : Nat) : Nat := (n / 2 ^ i) % 2

def weight (k n : Nat) : Nat :=
  (Finset.range k).sum (fun i => bit n i)

def mersenne (k : Nat) : Nat := 2 ^ k - 1

def pairPredicate (k t a b : Nat) : Prop :=
  a < mersenne k ∧ b < mersenne k ∧
    (a + b) % mersenne k = t % mersenne k ∧
    weight k a + weight k b < k

instance pairPredicateDecidable (k t : Nat) :
    DecidablePred (fun p : Nat × Nat => pairPredicate k t p.1 p.2) := by
  intro p
  unfold pairPredicate
  infer_instance

def pairCount (k t : Nat) : Nat :=
  letI := pairPredicateDecidable k t
  ((Finset.range (mersenne k)).product (Finset.range (mersenne k))).filter
    (fun p => pairPredicate k t p.1 p.2) |>.card

def TuDengConjecture : Prop :=
  ∀ {k t : Nat}, 2 ≤ k → 1 ≤ t → t ≤ mersenne k - 1 →
    pairCount k t ≤ 2 ^ (k - 1)

def circularDecrease (k t x : Nat) : Prop :=
  weight k ((x + t) % mersenne k) < weight k x

instance circularDecreaseDecidable (k t : Nat) :
    DecidablePred (circularDecrease k t) := by
  intro x
  unfold circularDecrease
  infer_instance

def circularCount (k t : Nat) : Nat :=
  letI := circularDecreaseDecidable k t
  (Finset.range (2 ^ k)).filter (circularDecrease k t) |>.card

def finitePairBound (limit : Nat) : Prop :=
  (List.range (limit + 1)).all (fun k =>
    (List.range (mersenne k)).all (fun t =>
      decide (pairCount k t ≤ 2 ^ (k - 1)))) = true

def finiteCircularBound (limit : Nat) : Prop :=
  (List.range (limit + 1)).all (fun k =>
    (List.range (mersenne k)).all (fun t =>
      decide (circularCount k t ≤ 2 ^ (k - 1)))) = true

def finitePairCircularBridge (limit : Nat) : Prop :=
  (List.range (limit + 1)).all (fun k =>
    (List.range (mersenne k)).all (fun t =>
      decide (pairCount k t = circularCount k t))) = true

theorem tuDeng_pair_circular_bridge_through_eight :
    finitePairCircularBridge 8 := by
  unfold finitePairCircularBridge
  native_decide

theorem tuDeng_circular_bound_through_eight :
    finiteCircularBound 8 := by
  unfold finiteCircularBound
  native_decide

theorem tuDeng_pair_bound_through_eight :
    finitePairBound 8 := by
  unfold finitePairBound
  native_decide

theorem tuDeng_pair_bound_of_word_length_le_eight
    {k t : Nat} (hk : k ≤ 8) (ht : t < mersenne k) :
    pairCount k t ≤ 2 ^ (k - 1) := by
  have h := tuDeng_pair_bound_through_eight
  unfold finitePairBound at h
  have hk' : k ∈ List.range (8 + 1) := by
    simp only [List.mem_range]
    omega
  have ht' : t ∈ List.range (mersenne k) := by
    simpa only [List.mem_range] using ht
  have hkall := List.all_eq_true.mp h k hk'
  have htall := List.all_eq_true.mp hkall t ht'
  exact of_decide_eq_true htall

theorem tuDeng_conjecture_for_k_le_eight
    {k t : Nat} (_hk : 2 ≤ k) (hk8 : k ≤ 8)
    (ht : 1 ≤ t) (htM : t ≤ mersenne k - 1) :
    pairCount k t ≤ 2 ^ (k - 1) := by
  apply tuDeng_pair_bound_of_word_length_le_eight hk8
  omega

theorem tuDeng_circular_bound_of_word_length_le_eight
    {k t : Nat} (hk : k ≤ 8) (ht : t < mersenne k) :
    circularCount k t ≤ 2 ^ (k - 1) := by
  have h := tuDeng_circular_bound_through_eight
  unfold finiteCircularBound at h
  have hk' : k ∈ List.range (8 + 1) := by
    simp only [List.mem_range]
    omega
  have ht' : t ∈ List.range (mersenne k) := by
    simpa only [List.mem_range] using ht
  have hkall := List.all_eq_true.mp h k hk'
  have htall := List.all_eq_true.mp hkall t ht'
  exact of_decide_eq_true htall

theorem tuDeng_k4_t5_exact :
    pairCount 4 5 = 8 ∧ circularCount 4 5 = 8 := by
  native_decide

end CryptoFrontierAtlas

import LeanCipher.F2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic

open scoped BigOperators

namespace LeanCipher

/-!
General semantics for symmetric Boolean functions.

This module is intentionally proof-first and dimension-generic.  Fixed-size
search artifacts may use these definitions later, but the definitions and the
first bridge theorem below do not depend on a chosen dimension or on exhaustive
enumeration.
-/

def HammingWeightF2 {n : Nat} (x : F2Vec n) : Nat :=
  (Finset.univ.filter (fun i : Fin n => x i = 1)).card

def DotF2 {n : Nat} (x y : F2Vec n) : ZMod 2 :=
  ∑ i : Fin n, x i * y i

def BitToSign (b : ZMod 2) : Int :=
  if b = 0 then 1 else -1

def SymBoolFun (n : Nat) : Type :=
  F2Vec n -> ZMod 2

def Walsh {n : Nat} (f : SymBoolFun n) (y : F2Vec n) : Int :=
  ∑ x : F2Vec n, BitToSign (f x + DotF2 x y)

def SymmetricByWeightProfile {n : Nat} (profile : Nat -> ZMod 2) : SymBoolFun n :=
  fun x => profile (HammingWeightF2 x)

def IsSymmetricBoolFun {n : Nat} (f : SymBoolFun n) : Prop :=
  ∃ profile : Nat -> ZMod 2, f = SymmetricByWeightProfile profile

def KrawtchoukWeightSlice {n : Nat}
    (profile : Nat -> ZMod 2) (y : F2Vec n) (r : Nat) : Int :=
  ∑ x ∈ (Finset.univ.filter (fun x : F2Vec n => HammingWeightF2 x = r)),
    BitToSign (profile r + DotF2 x y)

def CorrelationImmune {n : Nat} (t : Nat) (f : SymBoolFun n) : Prop :=
  ∀ y : F2Vec n, y ≠ 0 -> HammingWeightF2 y <= t -> Walsh f y = 0

def BalancedByWalsh {n : Nat} (f : SymBoolFun n) : Prop :=
  Walsh f 0 = 0

def Resilient {n : Nat} (t : Nat) (f : SymBoolFun n) : Prop :=
  BalancedByWalsh f ∧ CorrelationImmune t f

def IsAffineBoolFun {n : Nat} (f : SymBoolFun n) : Prop :=
  ∃ a : F2Vec n, ∃ c : ZMod 2, ∀ x : F2Vec n, f x = DotF2 a x + c

def IsNonAffineBoolFun {n : Nat} (f : SymBoolFun n) : Prop :=
  ¬ IsAffineBoolFun f

def ExistsNonAffineThreeResilientSymmetric : Prop :=
  ∃ n : Nat, ∃ f : SymBoolFun n,
    IsSymmetricBoolFun f ∧ IsNonAffineBoolFun f ∧ Resilient 3 f

theorem hammingWeightF2_le_dim {n : Nat} (x : F2Vec n) :
    HammingWeightF2 x <= n := by
  unfold HammingWeightF2
  have hle :
      (Finset.univ.filter (fun i : Fin n => x i = 1)).card <=
        (Finset.univ : Finset (Fin n)).card :=
    Finset.card_filter_le _ _
  simpa using hle

theorem hammingWeightF2_mem_range_succ {n : Nat} (x : F2Vec n) :
    HammingWeightF2 x ∈ Finset.range (n + 1) := by
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hammingWeightF2_le_dim x))

theorem symmetric_walsh_eq_krawtchouk_weight_sum {n : Nat}
    (profile : Nat -> ZMod 2) (y : F2Vec n) :
    Walsh (SymmetricByWeightProfile profile) y =
      ∑ r ∈ Finset.range (n + 1), KrawtchoukWeightSlice profile y r := by
  classical
  unfold Walsh SymmetricByWeightProfile KrawtchoukWeightSlice
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (F2Vec n)))
      (t := Finset.range (n + 1))
      (g := fun x : F2Vec n => HammingWeightF2 x)
      (h := fun x _ => hammingWeightF2_mem_range_succ x)
      (f := fun x : F2Vec n =>
        BitToSign (profile (HammingWeightF2 x) + DotF2 x y))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro x hx
  have hx_weight : HammingWeightF2 x = r := (Finset.mem_filter.mp hx).2
  rw [hx_weight]

end LeanCipher

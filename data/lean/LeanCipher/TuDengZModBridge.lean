import LeanCipher.TuDengBooleanBridge
import LeanCipher.TuDengCyclic

namespace LeanCipher.TuDengZModBridge

open LeanCipher

variable {k : Nat} [NeZero k]

theorem finEquiv_apply_eq_natCast (i : Fin k) :
    ZMod.finEquiv k i = (i.val : ZMod k) := by
  simpa [TuDengCyclic.cycleEquiv] using
    (TuDengCyclic.cycleEquiv_apply (k := k) (0 : ZMod k) i)

@[simp] theorem finZModWordEquiv_apply_finEquiv
    (x : Fin k -> Bool) (i : Fin k) :
    TuDengBooleanBridge.finZModWordEquiv k x (ZMod.finEquiv k i) = x i := by
  simp [TuDengBooleanBridge.finZModWordEquiv]

def cyclicizeCarry (c : Fin (k + 1) -> Bool) :
    TuDengCyclic.CarryWord k :=
  fun j => c ((ZMod.finEquiv k).symm j).castSucc = true

@[simp] theorem cyclicizeCarry_finEquiv
    (c : Fin (k + 1) -> Bool) (i : Fin k) :
    cyclicizeCarry c (ZMod.finEquiv k i) ↔ c i.castSucc = true := by
  simp [cyclicizeCarry]

theorem cyclicizeCarry_succ
    {c : Fin (k + 1) -> Bool}
    (hclosed : c (Fin.last k) = c 0) (i : Fin k) :
    cyclicizeCarry c (ZMod.finEquiv k i + 1) ↔ c i.succ = true := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      refine Fin.lastCases ?_ (fun r => ?_) i
      · have hz : (ZMod.finEquiv (n + 1) (Fin.last n) + 1) = 0 := by
          calc
            ZMod.finEquiv (n + 1) (Fin.last n) + 1 =
                (n : ZMod (n + 1)) + 1 := by
              rw [finEquiv_apply_eq_natCast]
              rfl
            _ = 0 := by
              simpa only [Nat.cast_add, Nat.cast_one] using
                (ZMod.natCast_self (n + 1))
        rw [hz]
        change c 0 = true ↔ c (Fin.last n).succ = true
        have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
          apply Fin.ext
          rfl
        rw [hlast, hclosed]
      · have hz :
            ZMod.finEquiv (n + 1) r.castSucc + 1 =
              ZMod.finEquiv (n + 1) r.succ := by
          calc
            ZMod.finEquiv (n + 1) r.castSucc + 1 =
                (r.val : ZMod (n + 1)) + 1 := by
              rw [finEquiv_apply_eq_natCast]
              rfl
            _ = (r.val + 1 : Nat) := by
              rw [Nat.cast_add, Nat.cast_one]
            _ = ZMod.finEquiv (n + 1) r.succ := by
              rw [finEquiv_apply_eq_natCast]
              rfl
        rw [hz, cyclicizeCarry_finEquiv]
        rfl

theorem cyclic_gate_iff_majority (state input target : Bool) :
    TuDengCyclic.gate (state = true) input target ↔
      TuDengPivotal.majority state input target = true := by
  cases state <;> cases input <;> cases target <;>
    simp [TuDengCyclic.gate, TuDengPivotal.majority]

theorem cyclicizeCarry_compatible
    {x d : Fin k -> Bool} {c : Fin (k + 1) -> Bool}
    (hclosed : c (Fin.last k) = c 0)
    (hcompatible : TuDengPivotal.carryCompatible x d c) :
    TuDengCyclic.CarryCompatible
      (TuDengBooleanBridge.finZModWordEquiv k x)
      (TuDengBooleanBridge.finZModWordEquiv k d)
      (cyclicizeCarry c) := by
  intro j
  let i := (ZMod.finEquiv k).symm j
  have hj : ZMod.finEquiv k i = j := (ZMod.finEquiv k).apply_symm_apply j
  rw [← hj, cyclicizeCarry_succ hclosed, cyclicizeCarry_finEquiv]
  simp only [finZModWordEquiv_apply_finEquiv]
  change c i.succ = true ↔
    TuDengCyclic.gate (c i.castSucc = true) (x i) (d i)
  rw [← hcompatible i]
  exact (cyclic_gate_iff_majority (c i.castSucc) (x i) (d i)).symm

noncomputable def propBool (p : Prop) : Bool := by
  classical
  exact if p then true else false

@[simp] theorem propBool_eq_true (p : Prop) : propBool p = true ↔ p := by
  classical
  simp [propBool]

@[simp] theorem propBool_eq_false (p : Prop) : propBool p = false ↔ ¬p := by
  classical
  simp [propBool]

noncomputable def linearizeCarry (p : TuDengCyclic.CarryWord k) :
    Fin (k + 1) -> Bool := by
  exact Fin.cases (propBool (p 0))
    (fun i => propBool (p (ZMod.finEquiv k i + 1)))

@[simp] theorem linearizeCarry_zero (p : TuDengCyclic.CarryWord k) :
    linearizeCarry p 0 = propBool (p 0) := by
  simp [linearizeCarry]

@[simp] theorem linearizeCarry_succ
    (p : TuDengCyclic.CarryWord k) (i : Fin k) :
    linearizeCarry p i.succ = propBool (p (ZMod.finEquiv k i + 1)) := by
  simp [linearizeCarry]

theorem finEquiv_castSucc_add_one {n : Nat} (i : Fin n) :
    ZMod.finEquiv (n + 1) i.castSucc + 1 =
      ZMod.finEquiv (n + 1) i.succ := by
  calc
    ZMod.finEquiv (n + 1) i.castSucc + 1 =
        (i.val : ZMod (n + 1)) + 1 := by
      rw [finEquiv_apply_eq_natCast]
      rfl
    _ = (i.val + 1 : Nat) := by
      rw [Nat.cast_add, Nat.cast_one]
    _ = ZMod.finEquiv (n + 1) i.succ := by
      rw [finEquiv_apply_eq_natCast]
      rfl

theorem finEquiv_last_add_one_eq_zero {n : Nat} :
    ZMod.finEquiv (n + 1) (Fin.last n) + 1 = 0 := by
  calc
    ZMod.finEquiv (n + 1) (Fin.last n) + 1 =
        (n : ZMod (n + 1)) + 1 := by
      rw [finEquiv_apply_eq_natCast]
      rfl
    _ = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ZMod.natCast_self (n + 1))

@[simp] theorem linearizeCarry_castSucc
    (p : TuDengCyclic.CarryWord k) (i : Fin k) :
    linearizeCarry p i.castSucc = propBool (p (ZMod.finEquiv k i)) := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      refine Fin.cases ?_ (fun r => ?_) i
      · simp [linearizeCarry, finEquiv_apply_eq_natCast]
      · change
          propBool (p (ZMod.finEquiv (n + 1) r.castSucc + 1)) =
            propBool (p (ZMod.finEquiv (n + 1) r.succ))
        rw [finEquiv_castSucc_add_one]

@[simp] theorem linearizeCarry_last (p : TuDengCyclic.CarryWord k) :
    linearizeCarry p (Fin.last k) = propBool (p 0) := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      have hlast : Fin.last (n + 1) = (Fin.last n).succ := by
        apply Fin.ext
        rfl
      rw [hlast, linearizeCarry_succ, finEquiv_last_add_one_eq_zero]

theorem linearizeCarry_closed (p : TuDengCyclic.CarryWord k) :
    linearizeCarry p (Fin.last k) = linearizeCarry p 0 := by
  rw [linearizeCarry_last, linearizeCarry_zero]

theorem linearizeCarry_compatible
    {x d : Fin k -> Bool} {p : TuDengCyclic.CarryWord k}
    (hp : TuDengCyclic.CarryCompatible
      (TuDengBooleanBridge.finZModWordEquiv k x)
      (TuDengBooleanBridge.finZModWordEquiv k d) p) :
    TuDengPivotal.carryCompatible x d (linearizeCarry p) := by
  intro i
  have hpi := hp (ZMod.finEquiv k i)
  simp only [finZModWordEquiv_apply_finEquiv] at hpi
  rw [linearizeCarry_castSucc, linearizeCarry_succ]
  by_cases hs : p (ZMod.finEquiv k i) <;>
    by_cases hn : p (ZMod.finEquiv k i + 1) <;>
    cases hx : x i <;> cases hd : d i <;>
    simp [hs, hn, hx, hd, TuDengCyclic.gate,
      TuDengPivotal.majority] at hpi ⊢

theorem cyclicizeCarry_linearizeCarry
    (p : TuDengCyclic.CarryWord k) :
    cyclicizeCarry (linearizeCarry p) = p := by
  funext j
  apply propext
  let i := (ZMod.finEquiv k).symm j
  have hj : ZMod.finEquiv k i = j := (ZMod.finEquiv k).apply_symm_apply j
  rw [← hj, cyclicizeCarry_finEquiv, linearizeCarry_castSucc]
  simp

theorem cyclicizeCarry_mono
    {c e : Fin (k + 1) -> Bool} (h : forall j, c j <= e j) :
    cyclicizeCarry c <= cyclicizeCarry e := by
  intro i hi
  change c ((ZMod.finEquiv k).symm i).castSucc = true at hi
  change e ((ZMod.finEquiv k).symm i).castSucc = true
  have hle := h ((ZMod.finEquiv k).symm i).castSucc
  rw [hi] at hle
  cases he : e ((ZMod.finEquiv k).symm i).castSucc with
  | false => exact ((by decide : ¬ (true <= false)) (by simpa [he] using hle)).elim
  | true => rfl

theorem cyclic_selectedCarry_eq
    (x d : Fin k -> Bool) :
    TuDengCyclic.selectedCarry
        (TuDengBooleanBridge.finZModWordEquiv k x)
        (TuDengBooleanBridge.finZModWordEquiv k d) =
      cyclicizeCarry (TuDengBooleanBridge.selectedCarry x d) := by
  let zx := TuDengBooleanBridge.finZModWordEquiv k x
  let zd := TuDengBooleanBridge.finZModWordEquiv k d
  let bc := TuDengBooleanBridge.selectedCarry x d
  let zc := TuDengCyclic.selectedCarry zx zd
  have hbc : TuDengCyclic.CarryCompatible zx zd (cyclicizeCarry bc) :=
    cyclicizeCarry_compatible
      (TuDengBooleanBridge.selectedCarry_closed x d)
      (TuDengBooleanBridge.selectedCarry_compatible x d)
  have hleft : cyclicizeCarry bc <= zc :=
    TuDengCyclic.compatible_le_selected hbc
  have hzc : TuDengPivotal.carryCompatible x d (linearizeCarry zc) :=
    linearizeCarry_compatible (TuDengCyclic.selectedCarry_compatible zx zd)
  have hlin : forall j, linearizeCarry zc j <= bc j :=
    TuDengBooleanBridge.compatible_le_selected hzc (linearizeCarry_closed zc)
  have hright : zc <= cyclicizeCarry bc := by
    rw [← cyclicizeCarry_linearizeCarry zc]
    exact cyclicizeCarry_mono hlin
  exact le_antisymm hright hleft

omit [NeZero k] in
theorem carryWeight_eq_true_card (c : Fin (k + 1) -> Bool) :
    TuDengBooleanBridge.carryWeight c =
      ((Finset.univ : Finset (Fin k)).filter
        (fun i => c i.castSucc = true)).card := by
  rw [Finset.card_filter]
  unfold TuDengBooleanBridge.carryWeight
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i.castSucc <;> simp

theorem weight_cyclicizeCarry (c : Fin (k + 1) -> Bool) :
    TuDengCyclic.weight (cyclicizeCarry c) =
      TuDengBooleanBridge.carryWeight c := by
  classical
  rw [carryWeight_eq_true_card]
  unfold TuDengCyclic.weight
  symm
  apply Finset.card_equiv (ZMod.finEquiv k).toEquiv
  intro i
  simp [TuDengCyclic.carrySet, cyclicizeCarry]

theorem selectedCarry_weight_eq (x d : Fin k -> Bool) :
    TuDengCyclic.weight
        (TuDengCyclic.selectedCarry
          (TuDengBooleanBridge.finZModWordEquiv k x)
          (TuDengBooleanBridge.finZModWordEquiv k d)) =
      TuDengBooleanBridge.carryWeight
        (TuDengBooleanBridge.selectedCarry x d) := by
  rw [cyclic_selectedCarry_eq, weight_cyclicizeCarry]

theorem inputWeight_reindex (x : Fin k -> Bool) :
    TuDengCyclic.inputWeight
        (TuDengBooleanBridge.finZModWordEquiv k x) =
      TuDengBooleanBridge.wordWeight x := by
  classical
  unfold TuDengCyclic.inputWeight TuDengBooleanBridge.wordWeight
  have hcard :
      ((Finset.univ : Finset (ZMod k)).filter
        (fun j => TuDengBooleanBridge.finZModWordEquiv k x j = true)).card =
      ((Finset.univ : Finset (Fin k)).filter (fun i => x i = true)).card := by
    symm
    apply Finset.card_equiv (ZMod.finEquiv k).toEquiv
    intro i
    simp [finZModWordEquiv_apply_finEquiv]
  rw [hcard]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases hxi : x i <;> simp

theorem IsZModBooleanBad_iff_cyclic_weight
    (t : Nat) (x : ZMod k -> Bool) :
    TuDengBooleanBridge.IsZModBooleanBad k t x ↔
      TuDengBooleanBridge.wordWeight (TuDengBooleanBridge.targetWord k t) <
        TuDengCyclic.weight
          (TuDengCyclic.selectedCarry x
            (TuDengBooleanBridge.zmodTargetWord k t)) := by
  let fx := (TuDengBooleanBridge.finZModWordEquiv k).symm x
  have hx : TuDengBooleanBridge.finZModWordEquiv k fx = x :=
    (TuDengBooleanBridge.finZModWordEquiv k).apply_symm_apply x
  rw [← hx]
  unfold TuDengBooleanBridge.IsZModBooleanBad
  rw [Equiv.symm_apply_apply]
  unfold TuDengBooleanBridge.IsBooleanBad TuDengBooleanBridge.zmodTargetWord
  rw [selectedCarry_weight_eq]

theorem IsZModBooleanBad_iff_cyclic_bad
    (t : Nat) (x : ZMod k -> Bool) :
    TuDengBooleanBridge.IsZModBooleanBad k t x ↔
      TuDengCyclic.inputWeight (TuDengBooleanBridge.zmodTargetWord k t) <
        TuDengCyclic.weight
          (TuDengCyclic.selectedCarry x
            (TuDengBooleanBridge.zmodTargetWord k t)) := by
  rw [IsZModBooleanBad_iff_cyclic_weight]
  rw [show TuDengBooleanBridge.zmodTargetWord k t =
      TuDengBooleanBridge.finZModWordEquiv k
        (TuDengBooleanBridge.targetWord k t) from rfl]
  rw [inputWeight_reindex]

noncomputable def cyclicBadFamily (k t : Nat) [NeZero k] :
    Finset (ZMod k -> Bool) := by
  classical
  exact (Finset.univ : Finset (ZMod k -> Bool)).filter fun x =>
    TuDengCyclic.inputWeight (TuDengBooleanBridge.zmodTargetWord k t) <
      TuDengCyclic.weight
        (TuDengCyclic.selectedCarry x
          (TuDengBooleanBridge.zmodTargetWord k t))

theorem cyclicBadFamily_eq_zmodBooleanBadFamily (k t : Nat) [NeZero k] :
    cyclicBadFamily k t = TuDengBooleanBridge.zmodBooleanBadFamily k t := by
  classical
  ext x
  simp only [cyclicBadFamily, TuDengBooleanBridge.zmodBooleanBadFamily,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact (IsZModBooleanBad_iff_cyclic_bad t x).symm

theorem circularDecreaseCount_eq_cyclicBadFamily_card
    {k t : Nat} [NeZero k] (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    circularDecreaseCount k t = (cyclicBadFamily k t).card := by
  rw [cyclicBadFamily_eq_zmodBooleanBadFamily,
    TuDengBooleanBridge.circularDecreaseCount_eq_zmodBooleanBadFamily_card
      hk ht]

theorem tuDengCount_eq_cyclicBadFamily_card
    {k t : Nat} [NeZero k] (hk : 2 <= k) (htPos : 1 <= t)
    (ht : t <= 2 ^ k - 2) :
    tuDengCount k t = (cyclicBadFamily k t).card := by
  rw [cyclicBadFamily_eq_zmodBooleanBadFamily,
    TuDengBooleanBridge.tuDengCount_eq_zmodBooleanBadFamily_card hk htPos ht]

end LeanCipher.TuDengZModBridge

import LeanCipher.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.ZMod.Basic
import LeanCipher.TuDeng
import LeanCipher.TuDengCarry
import LeanCipher.F2

/-!
This file contains mechanically assembled, kernel-checked lemmas used by the
Tu--Deng proof. It has been normalized for publication and checked with Lean's
default binder-annotation validation. No theorem is trusted merely because it
was generated: every declaration is replayed by the Lean kernel and covered by
`scripts/audit_lean_trust.py`.
-/

namespace LeanCipher.GeneratedVerifiedLemmas

open LeanCipher

theorem tu_deng_sum_representative_dichotomy
    (k t a b : ℕ)
    (_hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2)
    (ha : a ≤ 2 ^ k - 2)
    (hb : b ≤ 2 ^ k - 2)
    (hcong : Nat.ModEq (2 ^ k - 1) (a + b) t) :
    a + b = t ∨ a + b = t + (2 ^ k - 1) := by
  have ht_lt : t < 2 ^ k - 1 := by
    omega
  have hmod_pos : 0 < 2 ^ k - 1 := by
    omega
  have ha_lt : a < 2 ^ k - 1 := by
    omega
  have hb_lt : b < 2 ^ k - 1 := by
    omega
  have hsum_lt : a + b < (2 ^ k - 1) + (2 ^ k - 1) :=
    Nat.add_lt_add ha_lt hb_lt
  change (a + b) % (2 ^ k - 1) = t % (2 ^ k - 1) at hcong
  rw [Nat.mod_eq_of_lt ht_lt] at hcong
  let q : ℕ := (a + b) / (2 ^ k - 1)
  have hq_lt : q < 2 := by
    dsimp [q]
    apply (Nat.div_lt_iff_lt_mul hmod_pos).2
    simpa [two_mul] using hsum_lt
  have hq_cases : q = 0 ∨ q = 1 := by
    exact Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq_lt)
  have hdecomp :
      (a + b) % (2 ^ k - 1) + (2 ^ k - 1) * q = a + b := by
    dsimp [q]
    exact Nat.mod_add_div (a + b) (2 ^ k - 1)
  rcases hq_cases with hzero | hone
  · left
    rw [hzero, Nat.mul_zero, Nat.add_zero] at hdecomp
    exact hdecomp.symm.trans hcong
  · right
    rw [hone, Nat.mul_one] at hdecomp
    exact hdecomp.symm.trans
      (congrArg (fun n => n + (2 ^ k - 1)) hcong)




theorem tu_deng_cyclic_carry_trace_iff_sum
    (k a b t : ℕ)
    (q : Bool)
    (ha : a < 2 ^ k)
    (hb : b < 2 ^ k)
    (ht : t < 2 ^ k) :
    (a + b + q.toNat = t + (2 ^ k) * q.toNat) ↔
      ∃! c : Fin (k + 1) → Bool,
        c 0 = q ∧
          c (Fin.last k) = q ∧
            ∀ i : Fin k,
              (Nat.testBit a i.val).toNat +
                    (Nat.testBit b i.val).toNat +
                  (c i.castSucc).toNat =
                (Nat.testBit t i.val).toNat +
                  2 * (c i.succ).toNat := by
  classical
    have bool_ext (u v : Bool) (h : u.toNat = v.toNat) : u = v := by
      cases u <;> cases v <;> simp_all
    have bool_toNat_le_one (u : Bool) : u.toNat ≤ 1 := by
      cases u <;> simp
    have bit_zero (u : ℕ) : (Nat.testBit u 0).toNat = u % 2 := by
      have hu : u % 2 = 0 ∨ u % 2 = 1 := by
        omega
      rcases hu with hu | hu
      · simp [Nat.testBit, hu]
      · simp [Nat.testBit, hu]
    have bit_succ (u j : ℕ) :
        Nat.testBit u (j + 1) = Nat.testBit (u / 2) j := by
      simpa using Nat.testBit_succ u j
    have trace_unique :
        ∀ (n x y z : ℕ) (p r : Bool)
          (c d : Fin (n + 1) → Bool),
          (c 0 = p ∧
            c (Fin.last n) = r ∧
              ∀ i : Fin n,
                (Nat.testBit x i.val).toNat +
                      (Nat.testBit y i.val).toNat +
                    (c i.castSucc).toNat =
                  (Nat.testBit z i.val).toNat +
                    2 * (c i.succ).toNat) →
          (d 0 = p ∧
            d (Fin.last n) = r ∧
              ∀ i : Fin n,
                (Nat.testBit x i.val).toNat +
                      (Nat.testBit y i.val).toNat +
                    (d i.castSucc).toNat =
                  (Nat.testBit z i.val).toNat +
                    2 * (d i.succ).toNat) →
          c = d := by
      intro n x y z p r c d hc hd
      funext j
      induction j using Fin.induction with
      | zero =>
          exact hc.1.trans hd.1.symm
      | succ i hi =>
          have hci := hc.2.2 i
          have hdi := hd.2.2 i
          rw [hi] at hci
          apply bool_ext
          omega
    have trace_exists_iff :
        ∀ (n x y z : ℕ) (p r : Bool),
          x < 2 ^ n →
          y < 2 ^ n →
          z < 2 ^ n →
          (x + y + p.toNat = z + (2 ^ n) * r.toNat ↔
            ∃ c : Fin (n + 1) → Bool,
              c 0 = p ∧
                c (Fin.last n) = r ∧
                  ∀ i : Fin n,
                    (Nat.testBit x i.val).toNat +
                          (Nat.testBit y i.val).toNat +
                        (c i.castSucc).toNat =
                      (Nat.testBit z i.val).toNat +
                        2 * (c i.succ).toNat) := by
      intro n
      induction n with
      | zero =>
          intro x y z p r hx hy hz
          simp only [pow_zero] at hx hy hz
          have hx0 : x = 0 := by
            omega
          have hy0 : y = 0 := by
            omega
          have hz0 : z = 0 := by
            omega
          subst x
          subst y
          subst z
          constructor
          · intro h
            have hprNat : p.toNat = r.toNat := by
              simpa using h
            have hpr : p = r := bool_ext p r hprNat
            let c : Fin 1 → Bool := fun _ => p
            apply Exists.intro c
            constructor
            · rfl
            constructor
            · change p = r
              exact hpr
            · intro i
              exact Fin.elim0 i
          · rintro ⟨c, hc⟩
            have hlastzero : Fin.last 0 = (0 : Fin 1) := by
              apply Fin.ext
              rfl
            have hcr : c 0 = r := by
              rw [← hlastzero]
              exact hc.2.1
            have hpr : p = r := hc.1.symm.trans hcr
            simp [hpr]
      | succ n ih =>
          intro x y z p r hx hy hz
          have hxmod : x % 2 < 2 := Nat.mod_lt x (by omega)
          have hymod : y % 2 < 2 := Nat.mod_lt y (by omega)
          have hzmod : z % 2 < 2 := Nat.mod_lt z (by omega)
          have hpBound : p.toNat ≤ 1 := bool_toNat_le_one p
          let carryNat : ℕ := (x % 2 + y % 2 + p.toNat) / 2
          have hcarryLt : carryNat < 2 := by
            dsimp [carryNat]
            omega
          have hcarryCases : carryNat = 0 ∨ carryNat = 1 := by
            omega
          let s : Bool := decide (carryNat = 1)
          have hsNat : s.toNat = carryNat := by
            rcases hcarryCases with hzero | hone
            · simp [s, hzero]
            · simp [s, hone]
          have hsBound : s.toNat ≤ 1 := bool_toNat_le_one s
          have hsumMod :
              (x % 2 + y % 2 + p.toNat) % 2 < 2 :=
            Nat.mod_lt _ (by omega)
          have hsumSplit :
              x % 2 + y % 2 + p.toNat =
                (x % 2 + y % 2 + p.toNat) % 2 + 2 * s.toNat := by
            rw [hsNat]
            dsimp [carryNat]
            omega
          have hxSplit : x = x % 2 + 2 * (x / 2) := by
            omega
          have hySplit : y = y % 2 + 2 * (y / 2) := by
            omega
          have hzSplit : z = z % 2 + 2 * (z / 2) := by
            omega
          have hpow : 2 ^ Nat.succ n = 2 * (2 ^ n) := by
            rw [pow_succ]
            omega
          have hpowCarry :
              (2 ^ Nat.succ n) * r.toNat =
                2 * ((2 ^ n) * r.toNat) := by
            rw [hpow, Nat.mul_assoc]
          have hxHalf : x / 2 < 2 ^ n := by
            rw [hpow] at hx
            omega
          have hyHalf : y / 2 < 2 ^ n := by
            rw [hpow] at hy
            omega
          have hzHalf : z / 2 < 2 ^ n := by
            rw [hpow] at hz
            omega
          constructor
          · intro h
            rw [hpowCarry] at h
            have hrem :
                (x % 2 + y % 2 + p.toNat) % 2 = z % 2 := by
              omega
            have hlowNat :
                x % 2 + y % 2 + p.toNat =
                  z % 2 + 2 * s.toNat := by
              omega
            have hupper :
                x / 2 + y / 2 + s.toNat =
                  z / 2 + (2 ^ n) * r.toNat := by
              omega
            rcases
                (ih (x / 2) (y / 2) (z / 2) s r
                  hxHalf hyHalf hzHalf).mp hupper with
              ⟨d, hd⟩
            have hlowBit :
                (Nat.testBit x 0).toNat +
                      (Nat.testBit y 0).toNat +
                    p.toNat =
                  (Nat.testBit z 0).toNat + 2 * s.toNat := by
              simpa only [bit_zero] using hlowNat
            let c : Fin (Nat.succ n + 1) → Bool := Fin.cons p d
            have hc0 : c 0 = p := by
              rfl
            have hclast : c (Fin.last (Nat.succ n)) = r := by
              change d (Fin.last n) = r
              exact hd.2.1
            have hcrel :
                ∀ i : Fin (Nat.succ n),
                  (Nat.testBit x i.val).toNat +
                        (Nat.testBit y i.val).toNat +
                      (c i.castSucc).toNat =
                    (Nat.testBit z i.val).toNat +
                      2 * (c i.succ).toNat := by
              intro i
              cases i using Fin.cases with
              | zero =>
                  simpa [c, hd.1] using hlowBit
              | succ j =>
                  simpa [c, bit_succ] using hd.2.2 j
            exact ⟨c, hc0, hclast, hcrel⟩
          · rintro ⟨c, hc⟩
            have hlowBit := hc.2.2 (0 : Fin (Nat.succ n))
            have hcIncoming :
                c ((0 : Fin (Nat.succ n)).castSucc) = p := by
              simpa using hc.1
            rw [hcIncoming] at hlowBit
            change
              (Nat.testBit x 0).toNat +
                    (Nat.testBit y 0).toNat +
                  p.toNat =
                (Nat.testBit z 0).toNat +
                  2 * (c ((0 : Fin (Nat.succ n)).succ)).toNat at hlowBit
            have hlowNat :
                x % 2 + y % 2 + p.toNat =
                  z % 2 +
                    2 * (c ((0 : Fin (Nat.succ n)).succ)).toNat := by
              simpa only [bit_zero] using hlowBit
            let out : Bool := c ((0 : Fin (Nat.succ n)).succ)
            change
              x % 2 + y % 2 + p.toNat =
                z % 2 + 2 * out.toNat at hlowNat
            have houtBound : out.toNat ≤ 1 := bool_toNat_le_one out
            have houtNat : out.toNat = s.toNat := by
              omega
            have hout : out = s := bool_ext out s houtNat
            rw [hout] at hlowNat
            let d : Fin (n + 1) → Bool := fun j => c j.succ
            have hd0 : d 0 = s := by
              change out = s
              exact hout
            have hdlast : d (Fin.last n) = r := by
              change c (Fin.last (Nat.succ n)) = r
              exact hc.2.1
            have hdrel :
                ∀ j : Fin n,
                  (Nat.testBit (x / 2) j.val).toNat +
                        (Nat.testBit (y / 2) j.val).toNat +
                      (d j.castSucc).toNat =
                    (Nat.testBit (z / 2) j.val).toNat +
                      2 * (d j.succ).toNat := by
              intro j
              simpa [d, bit_succ] using hc.2.2 j.succ
            have hupper :
                x / 2 + y / 2 + s.toNat =
                  z / 2 + (2 ^ n) * r.toNat :=
              (ih (x / 2) (y / 2) (z / 2) s r
                hxHalf hyHalf hzHalf).mpr
                ⟨d, hd0, hdlast, hdrel⟩
            rw [hpowCarry]
            omega
    constructor
    · intro h
      rcases
          (trace_exists_iff k a b t q q ha hb ht).mp h with
        ⟨c, hc⟩
      apply ExistsUnique.intro c hc
      intro d hd
      exact trace_unique k a b t q q d c hd hc
    · rintro ⟨c, hc, hunique⟩
      exact
        (trace_exists_iff k a b t q q ha hb ht).mpr ⟨c, hc⟩




theorem tu_deng_cyclic_carry_weight_identity
    (k a b t : ℕ)
    (c : Fin (k + 1) → Bool)
    (hcycle : c 0 = c (Fin.last k))
    (hstep :
      ∀ i : Fin k,
        (Nat.testBit a i.val).toNat +
              (Nat.testBit b i.val).toNat +
            (c i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
            2 * (c i.succ).toNat) :
    let w := fun n : ℕ =>
      (Finset.univ : Finset (Fin k)).sum
        (fun i => (Nat.testBit n i.val).toNat)
    let carryWeight :=
      (Finset.univ : Finset (Fin k)).sum
        (fun i => (c i.castSucc).toNat)
    w a + w b = w t + carryWeight ∧
      ((w a + w b < k) ↔ 0 < k - (w t + carryWeight)) ∧
        (∀ n : ℕ, ¬ (w (2 ^ k - 1) + w n < k)) := by
  classical
    dsimp
    have hcarry :
        (Finset.univ : Finset (Fin k)).sum
            (fun i => (c i.succ).toNat) =
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (c i.castSucc).toNat) := by
      have htotal :
          (c 0).toNat +
              (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.succ).toNat) =
            (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.castSucc).toNat) +
              (c (Fin.last k)).toNat := by
        calc
          (c 0).toNat +
                (Finset.univ : Finset (Fin k)).sum
                  (fun i => (c i.succ).toNat) =
              (Finset.univ : Finset (Fin (k + 1))).sum
                (fun i => (c i).toNat) := by
                  rw [Fin.sum_univ_succ]
          _ =
              (Finset.univ : Finset (Fin k)).sum
                  (fun i => (c i.castSucc).toNat) +
                (c (Fin.last k)).toNat := by
                  rw [Fin.sum_univ_castSucc]
      have hends : (c 0).toNat = (c (Fin.last k)).toNat :=
        congrArg Bool.toNat hcycle
      omega
    have hsum :
        ((Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit a i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit b i.val).toNat)) +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.castSucc).toNat) =
          (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit t i.val).toNat) +
            2 * (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.succ).toNat) := by
      calc
        ((Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit a i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit b i.val).toNat)) +
              (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.castSucc).toNat) =
            (Finset.univ : Finset (Fin k)).sum
              (fun i =>
                (Nat.testBit a i.val).toNat +
                    (Nat.testBit b i.val).toNat +
                  (c i.castSucc).toNat) := by
                    simp only [Finset.sum_add_distrib]
        _ =
            (Finset.univ : Finset (Fin k)).sum
              (fun i =>
                (Nat.testBit t i.val).toNat +
                  2 * (c i.succ).toNat) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact hstep i
        _ =
            (Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit t i.val).toNat) +
              2 * (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.succ).toNat) := by
                  simp only [Finset.sum_add_distrib, Finset.mul_sum]
    have hweight :
        (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit a i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit b i.val).toNat) =
          (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit t i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.castSucc).toNat) := by
      omega
    constructor
    · exact hweight
    constructor
    · rw [hweight]
      omega
    · intro n hn
      have hallones :
          (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit (2 ^ k - 1) i.val).toNat) = k := by
        simp
      omega




theorem tu_deng_local_digit_equation_card
    (d cin cout : Bool) :
    Fintype.card
        {xy : Bool × Bool //
          xy.1.toNat + xy.2.toNat + cin.toNat =
            d.toNat + 2 * cout.toNat} =
      (if cin = Bool.not d then
        (if cout = d then 0 else 2)
      else 1) := by
  cases d <;> cases cin <;> cases cout <;> decide




theorem tu_deng_positive_carry_deficit_excludes_extra_representatives
    (k t : ℕ)
    (c : Fin (k + 1) → Bool)
    (a b : Fin (2 ^ k))
    (_hk : 2 ≤ k)
    (hcycle : c 0 = c (Fin.last k))
    (hstep :
      ∀ i : Fin k,
        (Nat.testBit a.val i.val).toNat +
              (Nat.testBit b.val i.val).toNat +
              (c i.castSucc).toNat =
            (Nat.testBit t i.val).toNat +
              2 * (c i.succ).toNat)
    (hdeficit :
      0 <
        k -
          ((Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit t i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.castSucc).toNat))) :
    a.val ≤ 2 ^ k - 2 ∧ b.val ≤ 2 ^ k - 2 := by
  classical
  have hcarry :=
    tu_deng_cyclic_carry_weight_identity
      k a.val b.val t c hcycle hstep
  dsimp only at hcarry
  have hstrict :
      (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit a.val i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit b.val i.val).toNat) < k :=
    hcarry.2.1.mpr hdeficit
  have hall :
      (Finset.univ : Finset (Fin k)).sum
          (fun i => (Nat.testBit (2 ^ k - 1) i.val).toNat) = k := by
    calc
      (Finset.univ : Finset (Fin k)).sum
          (fun i => (Nat.testBit (2 ^ k - 1) i.val).toNat) =
          (Finset.univ : Finset (Fin k)).sum (fun _ => 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [i.isLt]
      _ = k := by simp
  constructor
  · by_contra ha_bound
    have ha_lt : a.val < 2 ^ k := a.isLt
    have ha_eq : a.val = 2 ^ k - 1 := by omega
    rw [ha_eq, hall] at hstrict
    omega
  · by_contra hb_bound
    have hb_lt : b.val < 2 ^ k := b.isLt
    have hb_eq : b.val = 2 ^ k - 1 := by omega
    rw [hb_eq, hall] at hstrict
    omega




theorem tu_deng_fixed_carry_trace_fiber_card
    (k t : ℕ)
    (c : Fin (k + 1) → Bool) :
    Fintype.card
        {ab : Fin (2 ^ k) × Fin (2 ^ k) //
          ∀ i : Fin k,
            (Nat.testBit ab.1.val i.val).toNat +
                  (Nat.testBit ab.2.val i.val).toNat +
                  (c i.castSucc).toNat =
                (Nat.testBit t i.val).toNat +
                  2 * (c i.succ).toNat} =
      (Finset.univ : Finset (Fin k)).prod
        (fun i =>
          (if c i.castSucc =
                Bool.not (Nat.testBit t i.val) then
            (if c i.succ = Nat.testBit t i.val then 0 else 2)
          else 1)) := by
  classical
  let bits : Fin (2 ^ k) → Fin k → Bool :=
    fun n i => Nat.testBit n.val i.val
  have bits_injective : Function.Injective bits := by
    intro a b hab
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact congrFun hab ⟨i, hi⟩
    · have hki : k ≤ i := Nat.le_of_not_gt hi
      have hpow : 2 ^ k ≤ 2 ^ i := by
        exact Nat.pow_le_pow_right (by decide) hki
      have ha : a.val < 2 ^ i := lt_of_lt_of_le a.isLt hpow
      have hb : b.val < 2 ^ i := lt_of_lt_of_le b.isLt hpow
      rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]
  have bits_card :
      Fintype.card (Fin (2 ^ k)) = Fintype.card (Fin k → Bool) := by
    simp
  have bits_bijective : Function.Bijective bits := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨bits_injective, bits_card⟩
  let bitsEquiv : Fin (2 ^ k) ≃ (Fin k → Bool) :=
    Equiv.ofBijective bits bits_bijective
  let pairBitsEquiv :
      Fin (2 ^ k) × Fin (2 ^ k) ≃ (Fin k → Bool × Bool) :=
    { toFun := fun ab i =>
        (bitsEquiv ab.1 i, bitsEquiv ab.2 i)
      invFun := fun f =>
        (bitsEquiv.symm (fun i => (f i).1),
          bitsEquiv.symm (fun i => (f i).2))
      left_inv := by
        intro ab
        apply Prod.ext
        · exact bitsEquiv.left_inv ab.1
        · exact bitsEquiv.left_inv ab.2
      right_inv := by
        intro f
        funext i
        apply Prod.ext
        · exact congrFun
            (bitsEquiv.right_inv (fun j => (f j).1)) i
        · exact congrFun
            (bitsEquiv.right_inv (fun j => (f j).2)) i }
  let digitOK (i : Fin k) (xy : Bool × Bool) : Prop :=
    xy.1.toNat + xy.2.toNat + (c i.castSucc).toNat =
      (Nat.testBit t i.val).toNat + 2 * (c i.succ).toNat
  let sourceEquiv :
      {ab : Fin (2 ^ k) × Fin (2 ^ k) //
        ∀ i : Fin k,
          (Nat.testBit ab.1.val i.val).toNat +
                (Nat.testBit ab.2.val i.val).toNat +
                (c i.castSucc).toNat =
              (Nat.testBit t i.val).toNat +
                2 * (c i.succ).toNat} ≃
        {f : Fin k → Bool × Bool // ∀ i, digitOK i (f i)} :=
    Equiv.subtypeEquiv pairBitsEquiv (by
      intro ab
      rfl)
  let piEquiv :
      {f : Fin k → Bool × Bool // ∀ i, digitOK i (f i)} ≃
        ((i : Fin k) → {xy : Bool × Bool // digitOK i xy}) :=
    { toFun := fun f i => ⟨f.val i, f.property i⟩
      invFun := fun f =>
        ⟨fun i => (f i).val, fun i => (f i).property⟩
      left_inv := by
        intro f
        apply Subtype.ext
        rfl
      right_inv := by
        intro f
        funext i
        apply Subtype.ext
        rfl }
  calc
    Fintype.card
        {ab : Fin (2 ^ k) × Fin (2 ^ k) //
          ∀ i : Fin k,
            (Nat.testBit ab.1.val i.val).toNat +
                  (Nat.testBit ab.2.val i.val).toNat +
                  (c i.castSucc).toNat =
                (Nat.testBit t i.val).toNat +
                  2 * (c i.succ).toNat} =
        Fintype.card
          ((i : Fin k) → {xy : Bool × Bool // digitOK i xy}) := by
      exact Fintype.card_congr (sourceEquiv.trans piEquiv)
    _ = (Finset.univ : Finset (Fin k)).prod
          (fun i =>
            Fintype.card {xy : Bool × Bool // digitOK i xy}) := by
      exact Fintype.card_pi
    _ = (Finset.univ : Finset (Fin k)).prod
          (fun i =>
            (if c i.castSucc =
                  Bool.not (Nat.testBit t i.val) then
              (if c i.succ = Nat.testBit t i.val then 0 else 2)
            else 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      simpa [digitOK] using
        (tu_deng_local_digit_equation_card
          (Nat.testBit t i.val) (c i.castSucc) (c i.succ))




theorem tu_deng_two_le_pow_of_two_le
    (k : ℕ) (hk : 2 ≤ k) :
    2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      rw [pow_succ]
      have hpow_pos : 0 < 2 ^ k := pow_pos (by omega) k
      omega




theorem tu_deng_lt_pow_sub_one_iff_le_pow_sub_two
    (k n : ℕ) (hk : 2 ≤ k) :
    n < 2 ^ k - 1 ↔ n ≤ 2 ^ k - 2 := by
  have hpow : 2 ≤ 2 ^ k :=
    tu_deng_two_le_pow_of_two_le k hk
  omega




theorem tu_deng_mem_product_range_iff_bounded
    (k : ℕ) (hk : 2 ≤ k) (p : ℕ × ℕ) :
    p ∈ (Finset.range (2 ^ k - 1)).product
        (Finset.range (2 ^ k - 1)) ↔
      p.1 ≤ 2 ^ k - 2 ∧ p.2 ≤ 2 ^ k - 2 := by
  rcases p with ⟨a, b⟩
  constructor
  · intro hp
    have ha : a < 2 ^ k - 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hp).1
    have hb : b < 2 ^ k - 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hp).2
    exact
      ⟨(tu_deng_lt_pow_sub_one_iff_le_pow_sub_two k a hk).mp ha,
       (tu_deng_lt_pow_sub_one_iff_le_pow_sub_two k b hk).mp hb⟩
  · rintro ⟨ha, hb⟩
    apply Finset.mem_product.mpr
    exact
      ⟨Finset.mem_range.mpr
          ((tu_deng_lt_pow_sub_one_iff_le_pow_sub_two k a hk).mpr ha),
       Finset.mem_range.mpr
          ((tu_deng_lt_pow_sub_one_iff_le_pow_sub_two k b hk).mpr hb)⟩






theorem tu_deng_count_eq_explicit_bounded_pair_filter
    {k t : Nat}
    (hk : 2 ≤ k)
    (_ht_pos : 1 ≤ t)
    (_ht_upper : t ≤ 2 ^ k - 2) :
    tuDengCount k t =
      (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card := by
  unfold tuDengCount
  apply congrArg Finset.card
  ext ab
  rcases ab with ⟨a, b⟩
  have hpow : 2 ≤ 2 ^ k :=
    tu_deng_two_le_pow_of_two_le k hk
  have ha_bridge : a < 2 ^ k - 1 ↔ a ≤ 2 ^ k - 2 :=
    tu_deng_lt_pow_sub_one_iff_le_pow_sub_two k a hk
  have hb_bridge : b < 2 ^ k - 1 ↔ b ≤ 2 ^ k - 2 :=
    tu_deng_lt_pow_sub_one_iff_le_pow_sub_two k b hk
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hab, hp⟩
    have ha_lt : a < 2 ^ k - 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hab).1
    have hb_lt : b < 2 ^ k - 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hab).2
    have ha : a ≤ 2 ^ k - 2 := ha_bridge.mp ha_lt
    have hb : b ≤ 2 ^ k - 2 := hb_bridge.mp hb_lt
    have ha_pow : a < 2 ^ k := by omega
    have hb_pow : b < 2 ^ k := by omega
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha_pow,
        Finset.mem_range.mpr hb_pow⟩
    · unfold tuDengPair at hp
      exact ⟨ha, hb, hp.2.2⟩
  · rintro ⟨hab, ha, hb, hcong, hweight⟩
    have ha_lt : a < 2 ^ k - 1 := ha_bridge.mpr ha
    have hb_lt : b < 2 ^ k - 1 := hb_bridge.mpr hb
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha_lt,
        Finset.mem_range.mpr hb_lt⟩
    · unfold tuDengPair
      exact ⟨ha_lt, hb_lt, hcong, hweight⟩




theorem tu_deng_modeq_iff_sum_branches
    (k t a b : Nat)
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2)
    (ha : a ≤ 2 ^ k - 2)
    (hb : b ≤ 2 ^ k - 2) :
    Nat.ModEq (2 ^ k - 1) (a + b) t ↔
      a + b = t ∨ a + b = t + (2 ^ k - 1) := by
  constructor
  · intro hmod
    exact tu_deng_sum_representative_dichotomy
      k t a b hk ht_pos ht_upper ha hb hmod
  · intro hsum
    rcases hsum with hsum | hsum
    · rw [hsum]
    · rw [hsum]
      simp [Nat.ModEq]




theorem tu_deng_sum_branch_filters_disjoint
    {k t : Nat}
    (hk : 2 ≤ k) :
    Disjoint
      (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k))
      (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t + (2 ^ k - 1) ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)) := by
  apply Finset.disjoint_left.mpr
  intro ab hleft hright
  rw [Finset.mem_filter] at hleft hright
  rcases hleft with ⟨_, _, _, hsum_left, _⟩
  rcases hright with ⟨_, _, _, hsum_right, _⟩
  have hpow : 2 ≤ 2 ^ k := tu_deng_two_le_pow_of_two_le k hk
  have hmod_pos : 0 < 2 ^ k - 1 := by omega
  omega




theorem tu_deng_explicit_filter_eq_branch_union
    {k t : Nat}
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2) :
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)) =
      ((((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)) ∪
       (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t + (2 ^ k - 1) ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k))) := by
  ext ab
  constructor
  · intro hab
    rw [Finset.mem_filter] at hab
    rcases hab with ⟨hbase, ha, hb, hmod, hw⟩
    have hsum :=
      (tu_deng_modeq_iff_sum_branches
        k t ab.1 ab.2 hk ht_pos ht_upper ha hb).mp hmod
    rw [Finset.mem_union]
    rcases hsum with hsum | hsum
    · exact Or.inl (Finset.mem_filter.mpr ⟨hbase, ha, hb, hsum, hw⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hbase, ha, hb, hsum, hw⟩)
  · intro hab
    rw [Finset.mem_union] at hab
    rcases hab with hab | hab
    · rw [Finset.mem_filter] at hab ⊢
      rcases hab with ⟨hbase, ha, hb, hsum, hw⟩
      have hmod : Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t :=
        (tu_deng_modeq_iff_sum_branches
          k t ab.1 ab.2 hk ht_pos ht_upper ha hb).mpr (Or.inl hsum)
      exact ⟨hbase, ha, hb, hmod, hw⟩
    · rw [Finset.mem_filter] at hab ⊢
      rcases hab with ⟨hbase, ha, hb, hsum, hw⟩
      have hmod : Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t :=
        (tu_deng_modeq_iff_sum_branches
          k t ab.1 ab.2 hk ht_pos ht_upper ha hb).mpr (Or.inr hsum)
      exact ⟨hbase, ha, hb, hmod, hw⟩








theorem tu_deng_count_eq_sum_branch_cards
    {k t : Nat}
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2) :
    tuDengCount k t =
      (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card +
      (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t + (2 ^ k - 1) ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card := by
  rw [tu_deng_count_eq_explicit_bounded_pair_filter hk ht_pos ht_upper]
  let pairs := (Finset.range (2 ^ k)).product (Finset.range (2 ^ k))
  let congruenceFilter := pairs.filter
    (fun ab =>
      ab.1 ≤ 2 ^ k - 2 ∧
      ab.2 ≤ 2 ^ k - 2 ∧
      Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t ∧
      binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)
  let firstBranch := pairs.filter
    (fun ab =>
      ab.1 ≤ 2 ^ k - 2 ∧
      ab.2 ≤ 2 ^ k - 2 ∧
      ab.1 + ab.2 = t ∧
      binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)
  let secondBranch := pairs.filter
    (fun ab =>
      ab.1 ≤ 2 ^ k - 2 ∧
      ab.2 ≤ 2 ^ k - 2 ∧
      ab.1 + ab.2 = t + (2 ^ k - 1) ∧
      binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)
  have hunion : congruenceFilter = firstBranch ∪ secondBranch := by
    ext ab
    simp only [congruenceFilter, firstBranch, secondBranch,
      Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hab, ha, hb, hcong, hw⟩
      rcases tu_deng_sum_representative_dichotomy
          k t ab.1 ab.2 hk ht_pos ht_upper ha hb hcong with hsum | hsum
      · exact Or.inl ⟨hab, ha, hb, hsum, hw⟩
      · exact Or.inr ⟨hab, ha, hb, hsum, hw⟩
    · intro hab
      rcases hab with hfirst | hsecond
      · rcases hfirst with ⟨hpairs, ha, hb, hsum, hw⟩
        have hcong : Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t := by
          rw [hsum]
        exact ⟨hpairs, ha, hb, hcong, hw⟩
      · rcases hsecond with ⟨hpairs, ha, hb, hsum, hw⟩
        have hcong : Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t := by
          rw [hsum]
          simp [Nat.ModEq]
        exact ⟨hpairs, ha, hb, hcong, hw⟩
  have hmodulus_pos : 0 < 2 ^ k - 1 := by
    have hpow : 2 ≤ 2 ^ k := tu_deng_two_le_pow_of_two_le k hk
    omega
  have hdisjoint : Disjoint firstBranch secondBranch := by
    rw [Finset.disjoint_left]
    intro ab hfirst hsecond
    simp only [firstBranch, secondBranch, Finset.mem_filter] at hfirst hsecond
    rcases hfirst with ⟨_, _, _, hsum_first, _⟩
    rcases hsecond with ⟨_, _, _, hsum_second, _⟩
    omega
  calc
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          Nat.ModEq (2 ^ k - 1) (ab.1 + ab.2) t ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card =
        congruenceFilter.card := by rfl
    _ = (firstBranch ∪ secondBranch).card := by rw [hunion]
    _ = firstBranch.card + secondBranch.card :=
      Finset.card_union_of_disjoint hdisjoint
    _ =
      (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card +
      (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
        (fun ab =>
          ab.1 ≤ 2 ^ k - 2 ∧
          ab.2 ≤ 2 ^ k - 2 ∧
          ab.1 + ab.2 = t + (2 ^ k - 1) ∧
          binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card := by rfl




theorem tu_deng_endpoint_local_pair_forces_positive_deficit
    (k t : ℕ)
    (c : Fin (k + 1) → Bool)
    (endpoint : Bool)
    (a b : Fin (2 ^ k))
    (_hk : 2 ≤ k)
    (hstart : c 0 = endpoint)
    (hfinish : c (Fin.last k) = endpoint)
    (hstep :
      ∀ i : Fin k,
        (Nat.testBit a.val i.val).toNat +
              (Nat.testBit b.val i.val).toNat +
              (c i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
              2 * (c i.succ).toNat)
    (hstrict :
      (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit a.val i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit b.val i.val).toNat) <
        k) :
    0 <
      k -
        ((Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit t i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.castSucc).toNat)) := by
  have hcycle : c 0 = c (Fin.last k) := hstart.trans hfinish.symm
  have hweight :=
    tu_deng_cyclic_carry_weight_identity
      k a.val b.val t c hcycle hstep
  exact hweight.2.1.mp hstrict




theorem tu_deng_positive_deficit_local_pair_filters
    (k t : ℕ)
    (c : Fin (k + 1) → Bool)
    (a b : Fin (2 ^ k))
    (hk : 2 ≤ k)
    (hcycle : c 0 = c (Fin.last k))
    (hstep :
      ∀ i : Fin k,
        (Nat.testBit a.val i.val).toNat +
              (Nat.testBit b.val i.val).toNat +
              (c i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
              2 * (c i.succ).toNat)
    (hdeficit :
      0 <
        k -
          ((Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit t i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.castSucc).toNat))) :
    a.val ≤ 2 ^ k - 2 ∧
      b.val ≤ 2 ^ k - 2 ∧
      (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit a.val i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit b.val i.val).toNat) <
          k := by
  have hrange :=
    tu_deng_positive_carry_deficit_excludes_extra_representatives
      k t c a b hk hcycle hstep hdeficit
  have hweight :=
    tu_deng_cyclic_carry_weight_identity
      k a.val b.val t c hcycle hstep
  exact ⟨hrange.1, hrange.2, hweight.2.1.mpr hdeficit⟩




theorem tu_deng_positive_deficit_filtered_fiber_card_eq_local_fiber
    (k t : ℕ)
    (c : Fin (k + 1) → Bool)
    (hk : 2 ≤ k)
    (hcycle : c 0 = c (Fin.last k))
    (hdeficit :
      0 <
        k -
          ((Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit t i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.castSucc).toNat))) :
    Fintype.card
        {ab : Fin (2 ^ k) × Fin (2 ^ k) //
          (∀ i : Fin k,
            (Nat.testBit ab.1.val i.val).toNat +
                  (Nat.testBit ab.2.val i.val).toNat +
                  (c i.castSucc).toNat =
              (Nat.testBit t i.val).toNat +
                  2 * (c i.succ).toNat) ∧
            ab.1.val ≤ 2 ^ k - 2 ∧
            ab.2.val ≤ 2 ^ k - 2 ∧
            (Finset.univ : Finset (Fin k)).sum
                    (fun i => (Nat.testBit ab.1.val i.val).toNat) +
                  (Finset.univ : Finset (Fin k)).sum
                    (fun i => (Nat.testBit ab.2.val i.val).toNat) <
                k} =
      Fintype.card
        {ab : Fin (2 ^ k) × Fin (2 ^ k) //
          ∀ i : Fin k,
            (Nat.testBit ab.1.val i.val).toNat +
                  (Nat.testBit ab.2.val i.val).toNat +
                  (c i.castSucc).toNat =
              (Nat.testBit t i.val).toNat +
                  2 * (c i.succ).toNat} := by
  classical
  apply Fintype.card_congr
  exact
    { toFun := fun x => ⟨x.1, x.2.1⟩
      invFun := fun x =>
        ⟨x.1,
          ⟨x.2,
            tu_deng_positive_deficit_local_pair_filters
              k t c x.1.1 x.1.2 hk hcycle x.2 hdeficit⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }




theorem tu_deng_lt_pow_of_le_pow_sub_two
    (k n : ℕ)
    (hk : 2 ≤ k)
    (hn : n ≤ 2 ^ k - 2) :
    n < 2 ^ k := by
  have hpow : 2 ≤ 2 ^ k :=
    tu_deng_two_le_pow_of_two_le k hk
  omega




theorem tu_deng_cyclic_carry_trace_ext
    (k a b t : ℕ)
    (q : Bool)
    (c d : Fin (k + 1) → Bool)
    (hc :
      c 0 = q ∧
      c (Fin.last k) = q ∧
      ∀ i : Fin k,
        (Nat.testBit a i.val).toNat +
            (Nat.testBit b i.val).toNat +
            (c i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
            2 * (c i.succ).toNat)
    (hd :
      d 0 = q ∧
      d (Fin.last k) = q ∧
      ∀ i : Fin k,
        (Nat.testBit a i.val).toNat +
            (Nat.testBit b i.val).toNat +
            (d i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
            2 * (d i.succ).toNat) :
    c = d := by
  funext j
  induction j using Fin.induction with
  | zero => exact hc.1.trans hd.1.symm
  | succ i hi =>
    have hci := hc.2.2 i
    have hdi := hd.2.2 i
    rw [hi] at hci
    cases hcs : c i.succ <;> cases hds : d i.succ <;>
      simp [hcs, hds] at hci hdi ⊢ <;> omega




theorem tu_deng_cyclic_carry_trace_exists_unique_of_witness
    (k a b t : ℕ)
    (q : Bool)
    (c : Fin (k + 1) → Bool)
    (hc :
      c 0 = q ∧
      c (Fin.last k) = q ∧
      ∀ i : Fin k,
        (Nat.testBit a i.val).toNat +
            (Nat.testBit b i.val).toNat +
            (c i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
            2 * (c i.succ).toNat) :
    ∃! d : Fin (k + 1) → Bool,
      d 0 = q ∧
      d (Fin.last k) = q ∧
      ∀ i : Fin k,
        (Nat.testBit a i.val).toNat +
            (Nat.testBit b i.val).toNat +
            (d i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
            2 * (d i.succ).toNat := by
  exact ⟨c, hc, fun d hd =>
    tu_deng_cyclic_carry_trace_ext k a b t q d c hd hc⟩






theorem tu_deng_fixed_sum_branch_eq_carry_fiber_sum
    {k t : Nat}
    (hk : 2 ≤ k)
    (_ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2)
    (q : Bool) :
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        ab.1 + ab.2 + q.toNat = t + (2 ^ k) * q.toNat ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card =
      (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
        (fun c =>
          (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
            (fun ab =>
              ab.1 ≤ 2 ^ k - 2 ∧
              ab.2 ≤ 2 ^ k - 2 ∧
              binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k ∧
              c 0 = q ∧
              c (Fin.last k) = q ∧
              (∀ i : Fin k,
                (Nat.testBit ab.1 i.val).toNat +
                      (Nat.testBit ab.2 i.val).toNat +
                      (c i.castSucc).toNat =
                  (Nat.testBit t i.val).toNat +
                    2 * (c i.succ).toNat))).card) := by
  let B : Finset (Nat × Nat) :=
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        ab.1 + ab.2 + q.toNat = t + (2 ^ k) * q.toNat ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k))
  let F : (Fin (k + 1) → Bool) → Finset (Nat × Nat) := fun c =>
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k ∧
        c 0 = q ∧
        c (Fin.last k) = q ∧
        (∀ i : Fin k,
          (Nat.testBit ab.1 i.val).toNat +
                (Nat.testBit ab.2 i.val).toNat +
                (c i.castSucc).toNat =
            (Nat.testBit t i.val).toNat +
              2 * (c i.succ).toNat)))
  change B.card =
    (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
      (fun c => (F c).card)
  have ht_word : t < 2 ^ k :=
    tu_deng_lt_pow_of_le_pow_sub_two k t hk ht_upper
  have hB : B =
      (Finset.univ : Finset (Fin (k + 1) → Bool)).biUnion F := by
    apply Finset.ext
    intro ab
    constructor
    · intro hab
      rcases Finset.mem_filter.mp hab with
        ⟨hbase, ha_upper, hb_upper, hsum, hweight⟩
      have ha_word : ab.1 < 2 ^ k :=
        tu_deng_lt_pow_of_le_pow_sub_two k ab.1 hk ha_upper
      have hb_word : ab.2 < 2 ^ k :=
        tu_deng_lt_pow_of_le_pow_sub_two k ab.2 hk hb_upper
      rcases
          (tu_deng_cyclic_carry_trace_iff_sum
            k ab.1 ab.2 t q ha_word hb_word ht_word).mp hsum with
        ⟨c, hc, hc_unique⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ c,
        Finset.mem_filter.mpr
          ⟨hbase, ha_upper, hb_upper, hweight, hc⟩⟩
    · intro hab
      rcases Finset.mem_biUnion.mp hab with ⟨c, hc_univ, hc_mem⟩
      rcases Finset.mem_filter.mp hc_mem with
        ⟨hbase, ha_upper, hb_upper, hweight, hc⟩
      have ha_word : ab.1 < 2 ^ k :=
        tu_deng_lt_pow_of_le_pow_sub_two k ab.1 hk ha_upper
      have hb_word : ab.2 < 2 ^ k :=
        tu_deng_lt_pow_of_le_pow_sub_two k ab.2 hk hb_upper
      have hc_unique :=
        tu_deng_cyclic_carry_trace_exists_unique_of_witness
          k ab.1 ab.2 t q c hc
      have hsum :=
        (tu_deng_cyclic_carry_trace_iff_sum
          k ab.1 ab.2 t q ha_word hb_word ht_word).mpr hc_unique
      exact Finset.mem_filter.mpr
        ⟨hbase, ha_upper, hb_upper, hsum, hweight⟩
  have hdisj :
      (↑(Finset.univ : Finset (Fin (k + 1) → Bool)) :
        Set (Fin (k + 1) → Bool)).PairwiseDisjoint F := by
    intro c hc d hd hcd
    change Disjoint (F c) (F d)
    rw [Finset.disjoint_left]
    intro ab habc habd
    rcases Finset.mem_filter.mp habc with
      ⟨hbasec, hca, hcb, hcw, hc0, hclast, hceq⟩
    rcases Finset.mem_filter.mp habd with
      ⟨hbased, hda, hdb, hdw, hd0, hdlast, hdeq⟩
    have htrace : c = d :=
      tu_deng_cyclic_carry_trace_ext k ab.1 ab.2 t q c d
        ⟨hc0, hclast, hceq⟩ ⟨hd0, hdlast, hdeq⟩
    exact hcd htrace
  calc
    B.card =
        ((Finset.univ : Finset (Fin (k + 1) → Bool)).biUnion F).card := by
          rw [hB]
    _ = (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
        (fun c => (F c).card) := by
          exact Finset.card_biUnion hdisj




theorem tu_deng_binary_weight_up_to_succ
    (k n : Nat) :
    binaryWeightUpTo (k + 1) n =
      binaryWeightUpTo k n + (Nat.testBit n k).toNat := by
  have hbit : binaryBit n k = (Nat.testBit n k).toNat := by
    change n / 2 ^ k % 2 = (Nat.testBit n k).toNat
    simp only [Nat.testBit]
    rw [Nat.shiftRight_eq_div_pow]
    have hlt : n / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by omega)
    have hcases : n / 2 ^ k % 2 = 0 ∨ n / 2 ^ k % 2 = 1 := by
      omega
    rcases hcases with hzero | hone
    · simp [hzero]
    · simp [hone]
  simp [binaryWeightUpTo, Finset.sum_range_succ, hbit]




theorem tu_deng_test_bit_sum_succ
    (k n : Nat) :
    (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => (Nat.testBit n i.val).toNat) =
      (Finset.univ : Finset (Fin k)).sum
          (fun i => (Nat.testBit n i.val).toNat) +
        (Nat.testBit n k).toNat := by
  simpa using
    (Fin.sum_univ_castSucc
      (fun i : Fin (k + 1) => (Nat.testBit n i.val).toNat))






theorem tu_deng_binary_weight_up_to_eq_test_bit_sum
    (k n : Nat)
    (_hn : n < 2 ^ k) :
    binaryWeightUpTo k n =
      (Finset.univ : Finset (Fin k)).sum
        (fun i => (Nat.testBit n i.val).toNat) := by
  have h : ∀ k n : Nat,
      binaryWeightUpTo k n =
        (Finset.univ : Finset (Fin k)).sum
          (fun i => (Nat.testBit n i.val).toNat) := by
    intro k
    induction k with
    | zero =>
      intro n
      simp [binaryWeightUpTo]
    | succ k ih =>
      intro n
      rw [tu_deng_binary_weight_up_to_succ, tu_deng_test_bit_sum_succ, ih]
  exact h k n












theorem tu_deng_bool_fixed_sum_iff_modulus_branch_sum
    (k t a b : Nat)
    (q : Bool)
    (hk : 2 ≤ k) :
    a + b + q.toNat = t + (2 ^ k) * q.toNat ↔
      a + b = t + (2 ^ k - 1) * q.toNat := by
  cases q with
  | false =>
      simp [Bool.toNat]
  | true =>
      simp [Bool.toNat]
      have hpow : 2 ≤ 2 ^ k :=
        tu_deng_two_le_pow_of_two_le k hk
      omega




theorem tu_deng_modulus_branch_card_eq_bool_fixed_sum_branch_card
    {k t : Nat}
    (hk : 2 ≤ k)
    (q : Bool) :
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        ab.1 + ab.2 = t + (2 ^ k - 1) * q.toNat ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card =
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        ab.1 + ab.2 + q.toNat = t + (2 ^ k) * q.toNat ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card := by
  apply congrArg Finset.card
  ext ab
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hab, ha, hb, hsum, hweight⟩
    exact
      ⟨hab, ha, hb,
        (tu_deng_bool_fixed_sum_iff_modulus_branch_sum
          k t ab.1 ab.2 q hk).mpr hsum,
        hweight⟩
  · rintro ⟨hab, ha, hb, hsum, hweight⟩
    exact
      ⟨hab, ha, hb,
        (tu_deng_bool_fixed_sum_iff_modulus_branch_sum
          k t ab.1 ab.2 q hk).mp hsum,
        hweight⟩






theorem endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum
    (k n : Nat) :
    binaryWeightUpTo k n =
      (Finset.univ : Finset (Fin k)).sum
        (fun i => (Nat.testBit n i.val).toNat) := by
  have hbit (m j : Nat) :
      binaryBit m j = (Nat.testBit m j).toNat := by
    unfold binaryBit Nat.testBit
    rw [Nat.shiftRight_eq_div_pow]
    have hm :
        m / 2 ^ j % 2 = 0 ∨ m / 2 ^ j % 2 = 1 := by
      omega
    rcases hm with hm | hm
    · simp [hm]
    · simp [hm]
  induction k with
  | zero =>
      simp [binaryWeightUpTo]
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      change
        binaryWeightUpTo (Nat.succ k) n =
          (Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit n i.val).toNat) +
            (Nat.testBit n k).toNat
      rw [← ih]
      simp only [binaryWeightUpTo, Finset.sum_range_succ, hbit]




theorem endpoint_deficit_cases_round_2_tu_deng_fixed_carry_trace_positive_deficit_of_weight_lt
    (k t a b : Nat)
    (c : Fin (k + 1) → Bool)
    (hcycle : c 0 = c (Fin.last k))
    (hweight :
      binaryWeightUpTo k a + binaryWeightUpTo k b < k)
    (hsteps : ∀ i : Fin k,
      (Nat.testBit a i.val).toNat +
          (Nat.testBit b i.val).toNat +
          (c i.castSucc).toNat =
        (Nat.testBit t i.val).toNat +
          2 * (c i.succ).toNat) :
    0 < k -
      ((Finset.univ : Finset (Fin k)).sum
          (fun i => (Nat.testBit t i.val).toNat) +
        (Finset.univ : Finset (Fin k)).sum
          (fun i => (c i.castSucc).toNat)) := by
  have hcarry :
      (Finset.univ : Finset (Fin k)).sum
          (fun i => (c i.castSucc).toNat) =
        (Finset.univ : Finset (Fin k)).sum
          (fun i => (c i.succ).toNat) := by
    have hfull :
        (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.castSucc).toNat) +
            (c (Fin.last k)).toNat =
          (c 0).toNat +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.succ).toNat) := by
      rw [
        ← Fin.sum_univ_castSucc
          (fun i : Fin (k + 1) => (c i).toNat),
        Fin.sum_univ_succ
      ]
    have hcycleNat :
        (c 0).toNat = (c (Fin.last k)).toNat :=
      congrArg Bool.toNat hcycle
    omega
  have hsum :
      (Finset.univ : Finset (Fin k)).sum
          (fun i =>
            (Nat.testBit a i.val).toNat +
              (Nat.testBit b i.val).toNat +
              (c i.castSucc).toNat) =
        (Finset.univ : Finset (Fin k)).sum
          (fun i =>
            (Nat.testBit t i.val).toNat +
              2 * (c i.succ).toNat) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hsteps i
  have hsum' :
      (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit a i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit b i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (c i.castSucc).toNat) =
        (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit t i.val).toNat) +
          2 * (Finset.univ : Finset (Fin k)).sum
            (fun i => (c i.succ).toNat) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  rw [
    endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum k a,
    endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum k b
  ] at hweight
  omega








theorem tu_deng_fixed_carry_trace_fiber_card_zero_of_endpoint_mismatch
    (k t : Nat)
    (q : Bool)
    (c : Fin (k + 1) → Bool)
    (hendpoint : ¬ (c 0 = q ∧ c (Fin.last k) = q)) :
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k ∧
        c 0 = q ∧
        c (Fin.last k) = q ∧
        (∀ i : Fin k,
          (Nat.testBit ab.1 i.val).toNat +
                (Nat.testBit ab.2 i.val).toNat +
                (c i.castSucc).toNat =
            (Nat.testBit t i.val).toNat +
                2 * (c i.succ).toNat))).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.ext
  intro ab
  constructor
  · intro hab
    exfalso
    apply hendpoint
    have hp := (Finset.mem_filter.mp hab).2
    exact ⟨hp.2.2.2.1, hp.2.2.2.2.1⟩
  · intro hab
    simp at hab











theorem tu_deng_fixed_carry_filter_mem_endpoint_equalities
    {α : Type*} [DecidableEq α]
    {k : Nat}
    (S : Finset α)
    (P : α → Prop)
    [DecidablePred P]
    (c : Fin (k + 1) → Bool)
    (q : Bool)
    {x : α}
    (hx :
      x ∈ S.filter
        (fun y => P y ∧ (c 0 = q ∧ c (Fin.last k) = q))) :
    c 0 = q ∧ c (Fin.last k) = q := by
  have hfilter := Finset.mem_filter.mp hx
  have hpred := hfilter.2
  exact hpred.2






theorem tu_deng_filtered_local_pair_value_injective
    (k t : Nat)
    (c : Fin (k + 1) → Bool) :
    Function.Injective
      (fun x :
        {ab : Fin (2 ^ k) × Fin (2 ^ k) //
          (∀ i : Fin k,
            (Nat.testBit ab.1.val i.val).toNat +
                  (Nat.testBit ab.2.val i.val).toNat +
                (c i.castSucc).toNat =
              (Nat.testBit t i.val).toNat +
                2 * (c i.succ).toNat) ∧
          ab.1.val ≤ 2 ^ k - 2 ∧
          ab.2.val ≤ 2 ^ k - 2 ∧
          (Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit ab.1.val i.val).toNat) +
              (Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit ab.2.val i.val).toNat) < k} =>
        (x.val.1.val, x.val.2.val)) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg Prod.fst h
  · apply Fin.ext
    exact congrArg Prod.snd h












theorem tu_deng_positive_deficit_local_projection_image_card_eq_digit_product
    (k t : Nat)
    (c : Fin (k + 1) → Bool)
    (hk : 2 ≤ k)
    (hcycle : c 0 = c (Fin.last k))
    (hdeficit :
      0 < k -
        ((Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit t i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (c i.castSucc).toNat))) :
    ((Finset.univ :
        Finset
          {ab : Fin (2 ^ k) × Fin (2 ^ k) //
            (∀ i : Fin k,
              (Nat.testBit ab.1.val i.val).toNat +
                    (Nat.testBit ab.2.val i.val).toNat +
                  (c i.castSucc).toNat =
                (Nat.testBit t i.val).toNat +
                  2 * (c i.succ).toNat) ∧
            ab.1.val ≤ 2 ^ k - 2 ∧
            ab.2.val ≤ 2 ^ k - 2 ∧
            (Finset.univ : Finset (Fin k)).sum
                  (fun i => (Nat.testBit ab.1.val i.val).toNat) +
                (Finset.univ : Finset (Fin k)).sum
                  (fun i => (Nat.testBit ab.2.val i.val).toNat) < k}).image
      (fun x => (x.val.1.val, x.val.2.val))).card =
      (Finset.univ : Finset (Fin k)).prod
        (fun i =>
          if c i.castSucc = Bool.not (Nat.testBit t i.val) then
            if c i.succ = Nat.testBit t i.val then 0 else 2
          else 1) := by
  have hinj := tu_deng_filtered_local_pair_value_injective k t c
  rw [Finset.card_image_of_injective _ hinj]
  rw [Finset.card_univ]
  rw [tu_deng_positive_deficit_filtered_fiber_card_eq_local_fiber k t c hk hcycle hdeficit]
  exact tu_deng_fixed_carry_trace_fiber_card k t c








theorem tu_deng_positive_deficit_root_fiber_mem_iff_local_projection_image (k t : Nat) (q : Bool) (c : Fin (k + 1) → Bool) (ab : Nat × Nat) (hk : 2 ≤ k) (hstart : c 0 = q) (hfinish : c (Fin.last k) = q) (hdeficit : 0 < k - ((Finset.univ : Finset (Fin k)).sum (fun i => (Nat.testBit t i.val).toNat) + (Finset.univ : Finset (Fin k)).sum (fun i => (c i.castSucc).toNat))) : ab ∈ (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter (fun xy => xy.1 ≤ 2 ^ k - 2 ∧ xy.2 ≤ 2 ^ k - 2 ∧ binaryWeightUpTo k xy.1 + binaryWeightUpTo k xy.2 < k ∧ c 0 = q ∧ c (Fin.last k) = q ∧ (∀ i : Fin k, (Nat.testBit xy.1 i.val).toNat + (Nat.testBit xy.2 i.val).toNat + (c i.castSucc).toNat = (Nat.testBit t i.val).toNat + 2 * (c i.succ).toNat))) ↔ ab ∈ ((Finset.univ : Finset {xy : Fin (2 ^ k) × Fin (2 ^ k) // (∀ i : Fin k, (Nat.testBit xy.1.val i.val).toNat + (Nat.testBit xy.2.val i.val).toNat + (c i.castSucc).toNat = (Nat.testBit t i.val).toNat + 2 * (c i.succ).toNat) ∧ xy.1.val ≤ 2 ^ k - 2 ∧ xy.2.val ≤ 2 ^ k - 2 ∧ (Finset.univ : Finset (Fin k)).sum (fun i => (Nat.testBit xy.1.val i.val).toNat) + (Finset.univ : Finset (Fin k)).sum (fun i => (Nat.testBit xy.2.val i.val).toNat) < k}).image (fun x => (x.val.1.val, x.val.2.val))) := by
  have hpow : 2 ≤ 2 ^ k := tu_deng_two_le_pow_of_two_le k hk
  constructor
  · intro hab
    rcases Finset.mem_filter.mp hab with
      ⟨habprod, ha_le, hb_le, hweight, hc0, hclast, hstep⟩
    rcases Finset.mem_product.mp habprod with ⟨ha_range, hb_range⟩
    have ha_range_lt : ab.1 < 2 ^ k := Finset.mem_range.mp ha_range
    have hb_range_lt : ab.2 < 2 ^ k := Finset.mem_range.mp hb_range
    have ha_lt : ab.1 < 2 ^ k :=
      tu_deng_lt_pow_of_le_pow_sub_two k ab.1 hk ha_le
    have hb_lt : ab.2 < 2 ^ k :=
      tu_deng_lt_pow_of_le_pow_sub_two k ab.2 hk hb_le
    let a : Fin (2 ^ k) := ⟨ab.1, ha_lt⟩
    let b : Fin (2 ^ k) := ⟨ab.2, hb_lt⟩
    have hwa := tu_deng_binary_weight_up_to_eq_test_bit_sum k ab.1 ha_lt
    have hwb := tu_deng_binary_weight_up_to_eq_test_bit_sum k ab.2 hb_lt
    have hsum :
        (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit a.val i.val).toNat) +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (Nat.testBit b.val i.val).toNat) < k := by
      rw [← hwa, ← hwb]
      exact hweight
    let x : {xy : Fin (2 ^ k) × Fin (2 ^ k) //
        (∀ i : Fin k,
          (Nat.testBit xy.1.val i.val).toNat +
                (Nat.testBit xy.2.val i.val).toNat +
                (c i.castSucc).toNat =
            (Nat.testBit t i.val).toNat + 2 * (c i.succ).toNat) ∧
          xy.1.val ≤ 2 ^ k - 2 ∧
          xy.2.val ≤ 2 ^ k - 2 ∧
          (Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit xy.1.val i.val).toNat) +
              (Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit xy.2.val i.val).toNat) < k} :=
      ⟨(a, b), by
        refine ⟨?_, ?_, ?_, hsum⟩
        · simpa [a, b] using hstep
        · simpa [a] using ha_le
        · simpa [b] using hb_le⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ x, ?_⟩
    simp [x, a, b]
  · intro hab
    rcases Finset.mem_image.mp hab with ⟨x, hxuniv, hproj⟩
    subst ab
    have hstep :
        ∀ i : Fin k,
          (Nat.testBit x.val.1.val i.val).toNat +
                (Nat.testBit x.val.2.val i.val).toNat +
                (c i.castSucc).toNat =
            (Nat.testBit t i.val).toNat + 2 * (c i.succ).toNat :=
      x.property.1
    have hcycle : c 0 = c (Fin.last k) := hstart.trans hfinish.symm
    have hfilters :=
      tu_deng_positive_deficit_local_pair_filters
        k t c x.val.1 x.val.2 hk hcycle hstep hdeficit
    rcases hfilters with ⟨ha_le, hb_le, hsum⟩
    have ha_lt : x.val.1.val < 2 ^ k :=
      tu_deng_lt_pow_of_le_pow_sub_two k x.val.1.val hk ha_le
    have hb_lt : x.val.2.val < 2 ^ k :=
      tu_deng_lt_pow_of_le_pow_sub_two k x.val.2.val hk hb_le
    have hwa :=
      tu_deng_binary_weight_up_to_eq_test_bit_sum
        k x.val.1.val x.val.1.isLt
    have hwb :=
      tu_deng_binary_weight_up_to_eq_test_bit_sum
        k x.val.2.val x.val.2.isLt
    have hweight :
        binaryWeightUpTo k x.val.1.val +
          binaryWeightUpTo k x.val.2.val < k := by
      rw [hwa, hwb]
      exact hsum
    apply Finset.mem_filter.mpr
    refine ⟨?_, ha_le, hb_le, hweight, hstart, hfinish, hstep⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr ha_lt, Finset.mem_range.mpr hb_lt⟩


theorem tu_deng_positive_deficit_root_fiber_card_eq_digit_product (k t : Nat) (q : Bool) (c : Fin (k + 1) → Bool) (hk : 2 ≤ k) (hstart : c 0 = q) (hfinish : c (Fin.last k) = q) (hdeficit : 0 < k - ((Finset.univ : Finset (Fin k)).sum (fun i => (Nat.testBit t i.val).toNat) + (Finset.univ : Finset (Fin k)).sum (fun i => (c i.castSucc).toNat))) : (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter (fun ab => ab.1 ≤ 2 ^ k - 2 ∧ ab.2 ≤ 2 ^ k - 2 ∧ binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k ∧ c 0 = q ∧ c (Fin.last k) = q ∧ (∀ i : Fin k, (Nat.testBit ab.1 i.val).toNat + (Nat.testBit ab.2 i.val).toNat + (c i.castSucc).toNat = (Nat.testBit t i.val).toNat + 2 * (c i.succ).toNat))).card = (Finset.univ : Finset (Fin k)).prod (fun i => if c i.castSucc = Bool.not (Nat.testBit t i.val) then if c i.succ = Nat.testBit t i.val then 0 else 2 else 1) := by
  have hcycle : c 0 = c (Fin.last k) := hstart.trans hfinish.symm
  have hfiber := Finset.ext (fun ab =>
    tu_deng_positive_deficit_root_fiber_mem_iff_local_projection_image
      k t q c ab hk hstart hfinish hdeficit)
  rw [hfiber]
  exact tu_deng_positive_deficit_local_projection_image_card_eq_digit_product
    k t c hk hcycle hdeficit


theorem tu_deng_fixed_carry_trace_filtered_fiber_card (k t : Nat) (q : Bool) (c : Fin (k + 1) → Bool) (hk : 2 ≤ k) : (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter (fun ab => ab.1 ≤ 2 ^ k - 2 ∧ ab.2 ≤ 2 ^ k - 2 ∧ binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k ∧ c 0 = q ∧ c (Fin.last k) = q ∧ (∀ i : Fin k, (Nat.testBit ab.1 i.val).toNat + (Nat.testBit ab.2 i.val).toNat + (c i.castSucc).toNat = (Nat.testBit t i.val).toNat + 2 * (c i.succ).toNat))).card = if c 0 = q ∧ c (Fin.last k) = q ∧ 0 < k - ((Finset.univ : Finset (Fin k)).sum (fun i => (Nat.testBit t i.val).toNat) + (Finset.univ : Finset (Fin k)).sum (fun i => (c i.castSucc).toNat)) then (Finset.univ : Finset (Fin k)).prod (fun i => if c i.castSucc = Bool.not (Nat.testBit t i.val) then if c i.succ = Nat.testBit t i.val then 0 else 2 else 1) else 0 := by
  by_cases hstart : c 0 = q
  · by_cases hfinish : c (Fin.last k) = q
    · by_cases hdeficit :
        0 < k -
          ((Finset.univ : Finset (Fin k)).sum
              (fun i => (Nat.testBit t i.val).toNat) +
            (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.castSucc).toNat))
      · rw [tu_deng_positive_deficit_root_fiber_card_eq_digit_product
          k t q c hk hstart hfinish hdeficit]
        simp [hstart, hfinish, hdeficit]
      · have hcycle : c 0 = c (Fin.last k) := hstart.trans hfinish.symm
        have hzero :
            (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
              (fun ab =>
                ab.1 ≤ 2 ^ k - 2 ∧
                ab.2 ≤ 2 ^ k - 2 ∧
                binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k ∧
                c 0 = q ∧
                c (Fin.last k) = q ∧
                (∀ i : Fin k,
                  (Nat.testBit ab.1 i.val).toNat +
                      (Nat.testBit ab.2 i.val).toNat +
                      (c i.castSucc).toNat =
                    (Nat.testBit t i.val).toNat +
                      2 * (c i.succ).toNat))).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.ext
          intro ab
          constructor
          · intro hab
            rcases (Finset.mem_filter.mp hab).2 with
              ⟨_, _, hweight, _, _, hsteps⟩
            have hpositive :=
              endpoint_deficit_cases_round_2_tu_deng_fixed_carry_trace_positive_deficit_of_weight_lt
                k t ab.1 ab.2 c hcycle hweight hsteps
            exact (hdeficit hpositive).elim
          · simp
        rw [hzero]
        simp [hstart, hfinish, hdeficit]
    · have hendpoint : ¬ (c 0 = q ∧ c (Fin.last k) = q) := by
        intro h
        exact hfinish h.2
      rw [tu_deng_fixed_carry_trace_fiber_card_zero_of_endpoint_mismatch
        k t q c hendpoint]
      simp [hfinish]
  · have hendpoint : ¬ (c 0 = q ∧ c (Fin.last k) = q) := by
      intro h
      exact hstart h.1
    rw [tu_deng_fixed_carry_trace_fiber_card_zero_of_endpoint_mismatch
      k t q c hendpoint]
    simp [hstart]




theorem tu_deng_fixed_sum_branch_eq_carry_digit_product_sum
    {k t : Nat}
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2)
    (q : Bool) :
    (((Finset.range (2 ^ k)).product (Finset.range (2 ^ k))).filter
      (fun ab =>
        ab.1 ≤ 2 ^ k - 2 ∧
        ab.2 ≤ 2 ^ k - 2 ∧
        ab.1 + ab.2 + q.toNat = t + (2 ^ k) * q.toNat ∧
        binaryWeightUpTo k ab.1 + binaryWeightUpTo k ab.2 < k)).card =
      (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
        (fun c =>
          (if c 0 = q ∧
              c (Fin.last k) = q ∧
              0 <
                k -
                  ((Finset.univ : Finset (Fin k)).sum
                      (fun i => (Nat.testBit t i.val).toNat) +
                    (Finset.univ : Finset (Fin k)).sum
                      (fun i => (c i.castSucc).toNat))
            then
              (Finset.univ : Finset (Fin k)).prod
                (fun i =>
                  if c i.castSucc = Bool.not (Nat.testBit t i.val) then
                    if c i.succ = Nat.testBit t i.val then 0 else 2
                  else 1)
            else 0)) := by
  rw [tu_deng_fixed_sum_branch_eq_carry_fiber_sum hk ht_pos ht_upper q]
  apply Finset.sum_congr rfl
  intro c hc
  exact tu_deng_fixed_carry_trace_filtered_fiber_card k t q c hk









theorem tu_deng_count_eq_complete_carry_digit_product_aggregate
    {k t : Nat}
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2) :
    tuDengCount k t =
      (Finset.univ : Finset Bool).sum
        (fun q =>
          (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
            (fun c =>
              if c 0 = q ∧
                  c (Fin.last k) = q ∧
                  0 <
                    k -
                      ((Finset.univ : Finset (Fin k)).sum
                          (fun i => (Nat.testBit t i.val).toNat) +
                        (Finset.univ : Finset (Fin k)).sum
                          (fun i => (c i.castSucc).toNat))
              then
                (Finset.univ : Finset (Fin k)).prod
                  (fun i =>
                    if c i.castSucc =
                        Bool.not (Nat.testBit t i.val)
                    then
                      if c i.succ = Nat.testBit t i.val then 0 else 2
                    else 1)
              else 0)) := by
  rw [tu_deng_count_eq_sum_branch_cards hk ht_pos ht_upper]
  have hfalse :=
    (tu_deng_modulus_branch_card_eq_bool_fixed_sum_branch_card
        (k := k) (t := t) hk false).trans
      (tu_deng_fixed_sum_branch_eq_carry_digit_product_sum
        (k := k) (t := t) hk ht_pos ht_upper false)
  have htrue :=
    (tu_deng_modulus_branch_card_eq_bool_fixed_sum_branch_card
        (k := k) (t := t) hk true).trans
      (tu_deng_fixed_sum_branch_eq_carry_digit_product_sum
        (k := k) (t := t) hk ht_pos ht_upper true)
  simpa [Bool.toNat, Nat.add_comm] using congrArg₂ (· + ·) hfalse htrue














theorem tu_deng_count_eq_closed_admissible_carry_weight_sum
    {k t : Nat}
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2) :
    tuDengCount k t =
      (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
        (fun c =>
          if c 0 = c (Fin.last k) ∧
              0 <
                k -
                  ((Finset.univ : Finset (Fin k)).sum
                      (fun i => (Nat.testBit t i.val).toNat) +
                    (Finset.univ : Finset (Fin k)).sum
                      (fun i => (c i.castSucc).toNat))
          then
            if (∃ i : Fin k,
                c i.castSucc =
                    Bool.not (Nat.testBit t i.val) ∧
                  c i.succ = Nat.testBit t i.val)
            then (0 : Nat)
            else
              2 ^
                (((Finset.univ : Finset (Fin k)).filter
                    (fun i =>
                      c i.castSucc =
                        Bool.not (Nat.testBit t i.val))).card)
          else (0 : Nat)) := by
  rw [tu_deng_count_eq_complete_carry_digit_product_aggregate hk ht_pos ht_upper]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  have hprod :
      (∏ i : Fin k,
        if c i.castSucc = Bool.not (Nat.testBit t i.val) then
          if c i.succ = Nat.testBit t i.val then 0 else 2
        else 1) =
        if (∃ i : Fin k,
            c i.castSucc = Bool.not (Nat.testBit t i.val) ∧
              c i.succ = Nat.testBit t i.val)
        then 0
        else
          2 ^
            (((Finset.univ : Finset (Fin k)).filter
              (fun i =>
                c i.castSucc =
                  Bool.not (Nat.testBit t i.val))).card) := by
    split_ifs with hbad
    · rcases hbad with ⟨i, hi₁, hi₂⟩
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi₁, hi₂]
    · have hfactor : ∀ i : Fin k,
          (if c i.castSucc = Bool.not (Nat.testBit t i.val) then
              if c i.succ = Nat.testBit t i.val then 0 else 2
            else 1) =
            if c i.castSucc = Bool.not (Nat.testBit t i.val) then
              2
            else 1 := by
        intro i
        by_cases hi :
            c i.castSucc = Bool.not (Nat.testBit t i.val)
        · have hnext :
              c i.succ ≠ Nat.testBit t i.val := by
            intro hnext
            exact hbad ⟨i, hi, hnext⟩
          simp [hi, hnext]
        · simp [hi]
      have hpow : ∀ s : Finset (Fin k),
          s.prod
              (fun i =>
                if c i.castSucc =
                    Bool.not (Nat.testBit t i.val)
                then (2 : Nat)
                else 1) =
            2 ^
              (s.filter
                (fun i =>
                  c i.castSucc =
                    Bool.not (Nat.testBit t i.val))).card := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simp
        | @insert a s ha ih =>
            by_cases hpa :
                c a.castSucc = Bool.not (Nat.testBit t a.val)
            · rw [Finset.prod_insert ha, if_pos hpa]
              rw [Finset.filter_insert]
              rw [if_pos hpa]
              have haf : a ∉ s.filter (fun i =>
                  c i.castSucc = Bool.not (Nat.testBit t i.val)) := by
                intro hamem
                exact ha (Finset.mem_filter.mp hamem).1
              simp [haf, ih, pow_succ, Nat.mul_comm]
            · rw [Finset.prod_insert ha, if_neg hpa]
              rw [Finset.filter_insert]
              rw [if_neg hpa, ih]
              exact Nat.one_mul _
      calc
        (∏ i : Fin k,
            if c i.castSucc = Bool.not (Nat.testBit t i.val) then
              if c i.succ = Nat.testBit t i.val then 0 else 2
            else 1) =
            ∏ i : Fin k,
              if c i.castSucc =
                  Bool.not (Nat.testBit t i.val)
              then 2
              else 1 := by
                apply Finset.prod_congr rfl
                intro i hi
                exact hfactor i
        _ =
            2 ^
              (((Finset.univ : Finset (Fin k)).filter
                (fun i =>
                  c i.castSucc =
                    Bool.not (Nat.testBit t i.val))).card) :=
          hpow (Finset.univ : Finset (Fin k))
  rw [hprod]
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  cases h0 : c 0 <;>
    cases hl : c (Fin.last k) <;>
    simp



















































































theorem tu_deng_bool_digit_carry_accounting_step
    (x y d cin cout : Bool)
    (hstep :
      x.toNat + y.toNat + cin.toNat =
        d.toNat + 2 * cout.toNat) :
    d.toNat + 2 * cout.toNat +
          (if x = false ∧ y = false then 1 else 0) =
      1 + (if x = true ∧ y = true then 1 else 0) +
        cin.toNat := by
  cases x <;> cases y <;> cases d <;> cases cin <;> cases cout <;> simp_all




theorem tu_deng_cyclic_carry_sum_shift
    (k : Nat)
    (c : Fin (k + 1) → Bool)
    (hcycle : c 0 = c (Fin.last k)) :
    (Finset.univ : Finset (Fin k)).sum
          (fun i => (c i.succ).toNat) =
      (Finset.univ : Finset (Fin k)).sum
        (fun i => (c i.castSucc).toNat) := by
  have hhead :
      (Finset.univ : Finset (Fin (k + 1))).sum
            (fun i => (c i).toNat) =
        (c 0).toNat +
          (Finset.univ : Finset (Fin k)).sum
            (fun i => (c i.succ).toNat) := by
    simpa using
      (Fin.sum_univ_succ
        (f := fun i : Fin (k + 1) => (c i).toNat))
  have hlast :
      (Finset.univ : Finset (Fin (k + 1))).sum
            (fun i => (c i).toNat) =
        (Finset.univ : Finset (Fin k)).sum
              (fun i => (c i.castSucc).toNat) +
          (c (Fin.last k)).toNat := by
    simpa using
      (Fin.sum_univ_castSucc
        (f := fun i : Fin (k + 1) => (c i).toNat))
  have hends :
      (c 0).toNat = (c (Fin.last k)).toNat :=
    congrArg Bool.toNat hcycle
  omega




theorem tu_deng_finset_digit_carry_accounting
    (k t a b : Nat)
    (c : Fin (k + 1) → Bool)
    (S : Finset (Fin k))
    (hstep :
      ∀ i : Fin k,
        (Nat.testBit a i.val).toNat +
              (Nat.testBit b i.val).toNat +
            (c i.castSucc).toNat =
          (Nat.testBit t i.val).toNat +
            2 * (c i.succ).toNat) :
    (S).sum (fun i => (Nat.testBit t i.val).toNat) +
          2 * (S).sum (fun i => (c i.succ).toNat) +
          ((S).filter (fun i =>
            Nat.testBit a i.val = false ∧
              Nat.testBit b i.val = false)).card =
      S.card +
          ((S).filter (fun i =>
            Nat.testBit a i.val = true ∧
              Nat.testBit b i.val = true)).card +
        (S).sum (fun i => (c i.castSucc).toNat) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert i S hi ih =>
      have hlocal :=
        tu_deng_bool_digit_carry_accounting_step
          (Nat.testBit a i.val)
          (Nat.testBit b i.val)
          (Nat.testBit t i.val)
          (c i.castSucc)
          (c i.succ)
          (hstep i)
      cases ha : Nat.testBit a i.val <;>
        cases hb : Nat.testBit b i.val <;>
          simp [Finset.sum_insert, Finset.filter_insert, hi, ha, hb] at hlocal ⊢ <;>
          omega


theorem tu_deng_positive_carry_deficit_iff_match_balance (k t : Nat) (c : Fin (k + 1) → Bool) : (0 < k - ((Finset.univ : Finset (Fin k)).sum (fun i => (Nat.testBit t i.val).toNat) + (Finset.univ : Finset (Fin k)).sum (fun i => (c i.castSucc).toNat))) ↔ ((Finset.univ : Finset (Fin k)).filter (fun i => Nat.testBit t i.val = true ∧ c i.castSucc = true)).card < ((Finset.univ : Finset (Fin k)).filter (fun i => Nat.testBit t i.val = false ∧ c i.castSucc = false)).card := by
  classical
  have haccount :
      ∀ S : Finset (Fin k),
        S.sum (fun i => (Nat.testBit t i.val).toNat) +
            S.sum (fun i => (c i.castSucc).toNat) +
            (S.filter (fun i => Nat.testBit t i.val = false ∧
              c i.castSucc = false)).card =
          S.card +
            (S.filter (fun i => Nat.testBit t i.val = true ∧
              c i.castSucc = true)).card := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        cases hbit : Nat.testBit t i.val <;>
          cases hcarry : c i.castSucc <;>
          simp [Finset.filter_insert, hi, hbit, hcarry] at ih ⊢ <;> omega
  have huniv := haccount (Finset.univ : Finset (Fin k))
  simp only [Finset.card_univ, Fintype.card_fin] at huniv
  rw [Nat.sub_pos_iff_lt]
  omega








theorem tu_deng_complement_circular_endpoint_iff
    (k : Nat)
    (c : Fin (k + 1) → Bool) :
    ((!(c (0 : Fin (k + 1)))) =
      !(c (Fin.last k))) ↔
      c (0 : Fin (k + 1)) = c (Fin.last k) := by
  cases hzero : c (0 : Fin (k + 1)) <;>
    cases hlast : c (Fin.last k) <;>
    simp










theorem tu_deng_low_bit_complement_below_pow
    (k t : Nat)
    (ht : t < 2 ^ k)
    (i : Fin k) :
    Nat.testBit (2 ^ k - 1 - t) i.val =
      !(Nat.testBit t i.val) := by
  induction k generalizing t with
  | zero =>
      exact Fin.elim0 i
  | succ k ih =>
      have hpow : 0 < 2 ^ k := pow_pos (by omega) _
      rw [pow_succ] at ht ⊢
      cases i using Fin.cases with
      | zero =>
          unfold Nat.testBit
          have htmod_lt : t % 2 < 2 := Nat.mod_lt _ (by omega)
          have hnmod_lt : (2 ^ k * 2 - 1 - t) % 2 < 2 :=
            Nat.mod_lt _ (by omega)
          have htmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
          rcases htmod with htmod | htmod
          · have hcompmod : (2 ^ k * 2 - 1 - t) % 2 = 1 := by omega
            simp [htmod, hcompmod]
          · have hcompmod : (2 ^ k * 2 - 1 - t) % 2 = 0 := by omega
            simp [htmod, hcompmod]
      | succ i =>
          have htdiv : t / 2 < 2 ^ k := by omega
          have hdiv :
              (2 ^ k * 2 - 1 - t) / 2 = 2 ^ k - 1 - t / 2 := by
            omega
          change
            Nat.testBit (2 ^ k * 2 - 1 - t) (i.val + 1) =
              !(Nat.testBit t (i.val + 1))
          rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]
          exact ih (t / 2) htdiv i


theorem tu_deng_complemented_carry_trace_invariants
    {k t : Nat}
    (hk : 2 ≤ k)
    (_ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2)
    (c : Fin (k + 1) → Bool) :
    let tc := 2 ^ k - 1 - t
    let cc : Fin (k + 1) → Bool := fun j => Bool.not (c j)
    (cc 0 = cc (Fin.last k) ↔ c 0 = c (Fin.last k)) ∧
      ((∃ i : Fin k,
          cc i.castSucc = Bool.not (Nat.testBit tc i.val) ∧
            cc i.succ = Nat.testBit tc i.val) ↔
        (∃ i : Fin k,
          c i.castSucc = Bool.not (Nat.testBit t i.val) ∧
            c i.succ = Nat.testBit t i.val)) ∧
      (((Finset.univ : Finset (Fin k)).filter
          (fun i =>
            cc i.castSucc =
              Bool.not (Nat.testBit tc i.val))).card =
        ((Finset.univ : Finset (Fin k)).filter
          (fun i =>
            c i.castSucc =
              Bool.not (Nat.testBit t i.val))).card) ∧
      ((0 <
          k -
            ((Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit tc i.val).toNat) +
              (Finset.univ : Finset (Fin k)).sum
                (fun i => (cc i.castSucc).toNat))) ↔
        ((Finset.univ : Finset (Fin k)).filter
            (fun i =>
              Nat.testBit t i.val = false ∧
                c i.castSucc = false)).card <
          ((Finset.univ : Finset (Fin k)).filter
            (fun i =>
              Nat.testBit t i.val = true ∧
                c i.castSucc = true)).card) := by
  dsimp
  have ht_lt : t < 2 ^ k :=
    tu_deng_lt_pow_of_le_pow_sub_two k t hk ht_upper
  have hbit : ∀ i : Fin k,
      Nat.testBit (2 ^ k - 1 - t) i.val = !(Nat.testBit t i.val) := by
    intro i
    exact tu_deng_low_bit_complement_below_pow k t ht_lt i
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · constructor
    · rintro ⟨i, hprev, hnext⟩
      refine ⟨i, ?_, ?_⟩
      · rw [hbit i] at hprev
        cases htarget : Nat.testBit t i.val <;>
          cases hcarry : c i.castSucc <;>
          simp [htarget, hcarry] at hprev ⊢
      · rw [hbit i] at hnext
        cases htarget : Nat.testBit t i.val <;>
          cases hcarry : c i.succ <;>
          simp [htarget, hcarry] at hnext ⊢
    · rintro ⟨i, hprev, hnext⟩
      refine ⟨i, ?_, ?_⟩
      · rw [hbit i]
        cases htarget : Nat.testBit t i.val <;>
          cases hcarry : c i.castSucc <;>
          simp [htarget, hcarry] at hprev ⊢
      · rw [hbit i]
        cases htarget : Nat.testBit t i.val <;>
          cases hcarry : c i.succ <;>
          simp [htarget, hcarry] at hnext ⊢
  · apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hbit i]
    cases htarget : Nat.testBit t i.val <;>
      cases hcarry : c i.castSucc <;>
      simp
  · have h11 :
        (Finset.univ.filter (fun i : Fin k =>
          Nat.testBit (2 ^ k - 1 - t) i.val = true ∧
            (!(c i.castSucc)) = true)) =
        (Finset.univ.filter (fun i : Fin k =>
          Nat.testBit t i.val = false ∧ c i.castSucc = false)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hbit i]
      cases htarget : Nat.testBit t i.val <;>
        cases hcarry : c i.castSucc <;>
        simp
    have h00 :
        (Finset.univ.filter (fun i : Fin k =>
          Nat.testBit (2 ^ k - 1 - t) i.val = false ∧
            (!(c i.castSucc)) = false)) =
        (Finset.univ.filter (fun i : Fin k =>
          Nat.testBit t i.val = true ∧ c i.castSucc = true)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hbit i]
      cases htarget : Nat.testBit t i.val <;>
        cases hcarry : c i.castSucc <;>
        simp
    rw [tu_deng_positive_carry_deficit_iff_match_balance
      k (2 ^ k - 1 - t) (fun j => !(c j))]
    rw [h11, h00]


theorem tu_deng_complement_paired_gated_weight_le_closed_weight
    {k t : Nat}
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2)
    (c : Fin (k + 1) → Bool) :
    let tc : Nat := 2 ^ k - 1 - t
    let cc : Fin (k + 1) → Bool := fun j => Bool.not (c j)
    let supportedWeight :
        Nat → (Fin (k + 1) → Bool) → Nat :=
      fun u d =>
        if (∃ i : Fin k,
            d i.castSucc = Bool.not (Nat.testBit u i.val) ∧
              d i.succ = Nat.testBit u i.val)
        then 0
        else
          2 ^ (((Finset.univ : Finset (Fin k)).filter
            (fun i =>
              d i.castSucc = Bool.not (Nat.testBit u i.val))).card)
    let closedWeight :
        Nat → (Fin (k + 1) → Bool) → Nat :=
      fun u d =>
        if d 0 = d (Fin.last k) then supportedWeight u d else 0
    let gatedWeight :
        Nat → (Fin (k + 1) → Bool) → Nat :=
      fun u d =>
        if d 0 = d (Fin.last k) ∧
            0 <
              k -
                ((Finset.univ : Finset (Fin k)).sum
                    (fun i => (Nat.testBit u i.val).toNat) +
                  (Finset.univ : Finset (Fin k)).sum
                    (fun i => (d i.castSucc).toNat))
        then supportedWeight u d
        else 0
    gatedWeight t c + gatedWeight tc cc ≤ closedWeight t c := by
  dsimp only
  have hInv :=
    tu_deng_complemented_carry_trace_invariants hk ht_pos ht_upper c
  dsimp only at hInv
  rcases hInv with ⟨hclose, hforbid, hexponent, hcompDeficit⟩
  have horigDeficit :=
    tu_deng_positive_carry_deficit_iff_match_balance k t c
  by_cases hc : c 0 = c (Fin.last k)
  · have hcc : Bool.not (c 0) = Bool.not (c (Fin.last k)) :=
      hclose.mpr hc
    by_cases hf : ∃ i : Fin k,
        c i.castSucc = Bool.not (Nat.testBit t i.val) ∧
          c i.succ = Nat.testBit t i.val
    · have hfc : ∃ i : Fin k,
          Bool.not (c i.castSucc) =
              Bool.not (Nat.testBit (2 ^ k - 1 - t) i.val) ∧
            Bool.not (c i.succ) =
              Nat.testBit (2 ^ k - 1 - t) i.val :=
        hforbid.mpr hf
      by_cases hd : 0 <
          k -
            ((Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit t i.val).toNat) +
              (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.castSucc).toNat))
      · by_cases hdc : 0 <
            k -
              ((Finset.univ : Finset (Fin k)).sum
                  (fun i =>
                    (Nat.testBit (2 ^ k - 1 - t) i.val).toNat) +
                (Finset.univ : Finset (Fin k)).sum
                  (fun i => (Bool.not (c i.castSucc)).toNat))
        · have hlt := horigDeficit.mp hd
          have hltc := hcompDeficit.mp hdc
          exact (Nat.lt_asymm hlt hltc).elim
        · simp only [hc, hf, hfc, hd, hdc, true_and, if_true,
            if_false, add_zero, le_refl]
      · by_cases hdc : 0 <
            k -
              ((Finset.univ : Finset (Fin k)).sum
                  (fun i =>
                    (Nat.testBit (2 ^ k - 1 - t) i.val).toNat) +
                (Finset.univ : Finset (Fin k)).sum
                  (fun i => (Bool.not (c i.castSucc)).toNat))
        · simp only [hc, hf, hfc, hd, hdc, true_and, if_true,
            if_false, add_zero, le_refl]
        · simp only [hc, hf, hfc, hd, hdc, true_and, if_true,
            if_false, add_zero, le_refl]
    · have hfc : ¬ ∃ i : Fin k,
          Bool.not (c i.castSucc) =
              Bool.not (Nat.testBit (2 ^ k - 1 - t) i.val) ∧
            Bool.not (c i.succ) =
              Nat.testBit (2 ^ k - 1 - t) i.val := by
        intro h
        exact hf (hforbid.mp h)
      by_cases hd : 0 <
          k -
            ((Finset.univ : Finset (Fin k)).sum
                (fun i => (Nat.testBit t i.val).toNat) +
              (Finset.univ : Finset (Fin k)).sum
                (fun i => (c i.castSucc).toNat))
      · by_cases hdc : 0 <
            k -
              ((Finset.univ : Finset (Fin k)).sum
                  (fun i =>
                    (Nat.testBit (2 ^ k - 1 - t) i.val).toNat) +
                (Finset.univ : Finset (Fin k)).sum
                  (fun i => (Bool.not (c i.castSucc)).toNat))
        · have hlt := horigDeficit.mp hd
          have hltc := hcompDeficit.mp hdc
          exact (Nat.lt_asymm hlt hltc).elim
        · simp only [hc, hf, hfc, hd, hdc, true_and, if_true,
            if_false, add_zero, le_refl]
      · by_cases hdc : 0 <
            k -
              ((Finset.univ : Finset (Fin k)).sum
                  (fun i =>
                    (Nat.testBit (2 ^ k - 1 - t) i.val).toNat) +
                (Finset.univ : Finset (Fin k)).sum
                  (fun i => (Bool.not (c i.castSucc)).toNat))
        · rw [hexponent]
          simp only [hc, hf, hfc, hd, hdc, true_and, if_true,
            if_false, zero_add, le_refl]
        · simp only [hc, hf, hfc, hd, hdc, true_and, if_true,
            if_false, add_zero, Nat.zero_le]
  · have hcc : ¬ Bool.not (c 0) = Bool.not (c (Fin.last k)) := by
      intro h
      exact hc (hclose.mp h)
    simp only [hc, hcc, false_and, if_false, zero_add, le_refl]




theorem tu_deng_carry_trace_complement_involutive
    {k : Nat} :
    Function.Involutive
      (fun c : Fin (k + 1) → Bool => fun i => !(c i)) := by
  intro c
  funext i
  cases h : c i <;> simp [h]




theorem tu_deng_carry_trace_complement_sum_reindex
    {k : Nat}
    (F : (Fin (k + 1) → Bool) → Nat) :
    (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
        (fun c => F (fun i => !(c i))) =
      (Finset.univ : Finset (Fin (k + 1) → Bool)).sum F := by
  classical
  let e : (Fin (k + 1) → Bool) ≃ (Fin (k + 1) → Bool) :=
    { toFun := fun c i => !(c i)
      invFun := fun c i => !(c i)
      left_inv := tu_deng_carry_trace_complement_involutive
      right_inv := tu_deng_carry_trace_complement_involutive }
  simpa [e] using (Equiv.sum_comp e F)










theorem tu_deng_complement_gated_sum_reindex_and_paired_bound
    {k t : Nat}
    (hk : 2 ≤ k)
    (ht_pos : 1 ≤ t)
    (ht_upper : t ≤ 2 ^ k - 2) :
    let tc : Nat := 2 ^ k - 1 - t
    let complement :
        (Fin (k + 1) → Bool) → (Fin (k + 1) → Bool) :=
      fun c j => Bool.not (c j)
    let supportedWeight :
        Nat → (Fin (k + 1) → Bool) → Nat :=
      fun u c =>
        if (∃ i : Fin k,
            c i.castSucc = Bool.not (Nat.testBit u i.val) ∧
              c i.succ = Nat.testBit u i.val) then
          0
        else
          2 ^
            (((Finset.univ : Finset (Fin k)).filter
              (fun i =>
                c i.castSucc = Bool.not (Nat.testBit u i.val))).card)
    let closedWeight :
        Nat → (Fin (k + 1) → Bool) → Nat :=
      fun u c =>
        if c 0 = c (Fin.last k) then supportedWeight u c else 0
    let gatedWeight :
        Nat → (Fin (k + 1) → Bool) → Nat :=
      fun u c =>
        if c 0 = c (Fin.last k) ∧
            0 <
              k -
                ((Finset.univ : Finset (Fin k)).sum
                    (fun i => (Nat.testBit u i.val).toNat) +
                  (Finset.univ : Finset (Fin k)).sum
                    (fun i => (c i.castSucc).toNat))
        then supportedWeight u c
        else 0
    (∀ c : Fin (k + 1) → Bool, complement (complement c) = c) ∧
      ((Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc (complement c)) =
        (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc c)) ∧
      (((Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight t c)) +
        ((Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc c)) ≤
        (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => closedWeight t c)) := by
  classical
  let tc : Nat := 2 ^ k - 1 - t
  let complement :
      (Fin (k + 1) → Bool) → (Fin (k + 1) → Bool) :=
    fun c j => Bool.not (c j)
  let supportedWeight :
      Nat → (Fin (k + 1) → Bool) → Nat :=
    fun u c =>
      if (∃ i : Fin k,
          c i.castSucc = Bool.not (Nat.testBit u i.val) ∧
            c i.succ = Nat.testBit u i.val) then
        0
      else
        2 ^
          (((Finset.univ : Finset (Fin k)).filter
            (fun i =>
              c i.castSucc = Bool.not (Nat.testBit u i.val))).card)
  let closedWeight :
      Nat → (Fin (k + 1) → Bool) → Nat :=
    fun u c =>
      if c 0 = c (Fin.last k) then supportedWeight u c else 0
  let gatedWeight :
      Nat → (Fin (k + 1) → Bool) → Nat :=
    fun u c =>
      if c 0 = c (Fin.last k) ∧
          0 <
            k -
              ((Finset.univ : Finset (Fin k)).sum
                  (fun i => (Nat.testBit u i.val).toNat) +
                (Finset.univ : Finset (Fin k)).sum
                  (fun i => (c i.castSucc).toNat))
      then supportedWeight u c
      else 0
  change
    (∀ c : Fin (k + 1) → Bool, complement (complement c) = c) ∧
      ((Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc (complement c)) =
        (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc c)) ∧
      (((Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight t c)) +
        ((Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc c)) ≤
        (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => closedWeight t c))
  have hcomp :
      ∀ c : Fin (k + 1) → Bool, complement (complement c) = c := by
    exact tu_deng_carry_trace_complement_involutive
  have hsum :
      (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc (complement c)) =
        (Finset.univ : Finset (Fin (k + 1) → Bool)).sum
          (fun c => gatedWeight tc c) := by
    exact
      tu_deng_carry_trace_complement_sum_reindex
        (k := k) (fun c => gatedWeight tc c)
  have hpair (c : Fin (k + 1) → Bool) :
      gatedWeight t c + gatedWeight tc (complement c) ≤
        closedWeight t c := by
    exact
      tu_deng_complement_paired_gated_weight_le_closed_weight
        (k := k) (t := t) hk ht_pos ht_upper c
  refine ⟨hcomp, hsum, ?_⟩
  rw [← hsum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c hc
  exact hpair c

end LeanCipher.GeneratedVerifiedLemmas

import LeanCipher.TuDengBridge
import CryptoFrontierAtlas.TuDengPivotal

open scoped BigOperators

namespace LeanCipher.TuDengBooleanBridge

open LeanCipher
open LeanCipher.GeneratedVerifiedLemmas

/-! ## Exact finite-word encoding -/

def finToWord {k : Nat} (n : Fin (2 ^ k)) : Fin k -> Bool :=
  fun i => Nat.testBit n.val i.val

def wordToFin {k : Nat} (x : Fin k -> Bool) : Fin (2 ^ k) :=
  ⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x⟩

theorem finToWord_wordToFin {k : Nat} (x : Fin k -> Bool) :
    finToWord (wordToFin x) = x := by
  funext i
  simp [finToWord, wordToFin, i.isLt]

theorem wordToFin_finToWord {k : Nat} (n : Fin (2 ^ k)) :
    wordToFin (finToWord n) = n := by
  apply Fin.ext
  change Nat.ofBits (fun i : Fin k => Nat.testBit n.val i.val) = n.val
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt n.isLt]

def bitWordEquiv (k : Nat) : Fin (2 ^ k) ≃ (Fin k -> Bool) where
  toFun := finToWord
  invFun := wordToFin
  left_inv := wordToFin_finToWord
  right_inv := finToWord_wordToFin

def wordWeight {k : Nat} (x : Fin k -> Bool) : Nat :=
  (Finset.univ : Finset (Fin k)).sum fun i => (x i).toNat

theorem wordWeight_finToWord {k : Nat} (n : Fin (2 ^ k)) :
    wordWeight (finToWord n) = binaryWeightUpTo k n.val := by
  rw [endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum]
  rfl

def targetWord (k t : Nat) : Fin k -> Bool :=
  fun i => Nat.testBit t i.val

theorem wordWeight_targetWord (k t : Nat) :
    wordWeight (targetWord k t) = binaryWeightUpTo k t := by
  rw [endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum]
  rfl

/-! ## Greatest closed majority carry -/

def inputTargetList {k : Nat} (x d : Fin k -> Bool) : List (Bool × Bool) :=
  List.ofFn fun i => (x i, d i)

def carryFrom {k : Nat} (x d : Fin k -> Bool) (q : Bool) :
    Fin (k + 1) -> Bool :=
  fun j =>
    (inputTargetList x d).take j.val |>.foldl TuDengPivotal.gate q

@[simp] theorem carryFrom_zero {k : Nat} (x d : Fin k -> Bool) (q : Bool) :
    carryFrom x d q 0 = q := by
  simp [carryFrom]

theorem carryFrom_succ {k : Nat} (x d : Fin k -> Bool) (q : Bool)
    (i : Fin k) :
    carryFrom x d q i.succ =
      TuDengPivotal.majority (carryFrom x d q i.castSucc) (x i) (d i) := by
  unfold carryFrom
  change
    List.foldl TuDengPivotal.gate q
        ((inputTargetList x d).take (i.val + 1)) = _
  rw [List.take_add_one, List.foldl_append]
  simp [inputTargetList, TuDengPivotal.gate, i.isLt]

theorem carryFrom_last {k : Nat} (x d : Fin k -> Bool) (q : Bool) :
    carryFrom x d q (Fin.last k) =
      TuDengPivotal.propagate (inputTargetList x d) q := by
  unfold carryFrom TuDengPivotal.propagate
  change
    List.foldl TuDengPivotal.gate q ((inputTargetList x d).take k) =
      List.foldl TuDengPivotal.gate q (inputTargetList x d)
  have ht : (inputTargetList x d).take k = inputTargetList x d := by
    simp [inputTargetList]
  rw [ht]

def selectedInitial {k : Nat} (x d : Fin k -> Bool) : Bool :=
  TuDengPivotal.selectedInitial (inputTargetList x d)

def selectedCarry {k : Nat} (x d : Fin k -> Bool) : Fin (k + 1) -> Bool :=
  carryFrom x d (selectedInitial x d)

@[simp] theorem selectedCarry_zero {k : Nat} (x d : Fin k -> Bool) :
    selectedCarry x d 0 = selectedInitial x d := by
  simp [selectedCarry]

theorem selectedCarry_succ {k : Nat} (x d : Fin k -> Bool) (i : Fin k) :
    selectedCarry x d i.succ =
      TuDengPivotal.majority (selectedCarry x d i.castSucc) (x i) (d i) := by
  exact carryFrom_succ x d (selectedInitial x d) i

theorem selectedCarry_closed {k : Nat} (x d : Fin k -> Bool) :
    selectedCarry x d (Fin.last k) = selectedCarry x d 0 := by
  rw [selectedCarry, carryFrom_last, carryFrom_zero]
  exact TuDengPivotal.selectedInitial_fixed (inputTargetList x d)

theorem selectedCarry_compatible {k : Nat} (x d : Fin k -> Bool) :
    TuDengPivotal.carryCompatible x d (selectedCarry x d) := by
  intro i
  exact (selectedCarry_succ x d i).symm

theorem carryFrom_ext {k : Nat} {x d : Fin k -> Bool} {q : Bool}
    {c : Fin (k + 1) -> Bool}
    (hzero : c 0 = q)
    (hstep : forall i : Fin k,
      TuDengPivotal.majority (c i.castSucc) (x i) (d i) = c i.succ) :
    carryFrom x d q = c := by
  funext j
  induction j using Fin.induction with
  | zero => simpa using hzero.symm
  | succ i ih =>
      rw [carryFrom_succ, ih, hstep]

def WordLE {k : Nat} (x y : Fin k -> Bool) : Prop :=
  forall i, x i <= y i

theorem carryFrom_mono {k : Nat} {x y d : Fin k -> Bool} {q r : Bool}
    (hxy : WordLE x y) (hqr : q <= r) :
    forall j, carryFrom x d q j <= carryFrom y d r j := by
  intro j
  induction j using Fin.induction with
  | zero => simpa using hqr
  | succ i ih =>
      rw [carryFrom_succ, carryFrom_succ]
      exact TuDengPivotal.majority_mono ih (hxy i)

theorem selectedInitial_mono {k : Nat} {x y d : Fin k -> Bool}
    (hxy : WordLE x y) :
    selectedInitial x d <= selectedInitial y d := by
  unfold selectedInitial TuDengPivotal.selectedInitial
  rw [← carryFrom_last x d true, ← carryFrom_last y d true]
  exact carryFrom_mono hxy le_rfl (Fin.last k)

theorem selectedCarry_mono {k : Nat} {x y d : Fin k -> Bool}
    (hxy : WordLE x y) :
    forall j, selectedCarry x d j <= selectedCarry y d j := by
  intro j
  exact carryFrom_mono hxy (selectedInitial_mono hxy) j

theorem compatible_le_selected {k : Nat} {x d : Fin k -> Bool}
    {c : Fin (k + 1) -> Bool}
    (hcompatible : TuDengPivotal.carryCompatible x d c)
    (hclosed : c (Fin.last k) = c 0) :
    forall j, c j <= selectedCarry x d j := by
  let q := c 0
  have hfrom : carryFrom x d q = c := by
    apply carryFrom_ext rfl
    intro i
    exact hcompatible i
  have hfixed :
      TuDengPivotal.propagate (inputTargetList x d) q = q := by
    rw [← carryFrom_last, hfrom]
    exact hclosed
  have hq : q <= selectedInitial x d := by
    exact TuDengPivotal.fixed_initial_le_selected hfixed
  intro j
  have hmono := carryFrom_mono (x := x) (y := x) (d := d)
    (fun _ => le_rfl) hq j
  rw [hfrom] at hmono
  exact hmono

/-! ## From majority carries to ordinary digit equations -/

def sumBit (a b cin : Bool) : Bool :=
  Bool.xor (Bool.xor a b) cin

theorem sumBit_majority_identity (a b cin : Bool) :
    a.toNat + b.toNat + cin.toNat =
      (sumBit a b cin).toNat +
        2 * (TuDengPivotal.majority cin a b).toNat := by
  cases a <;> cases b <;> cases cin <;>
    decide

theorem majority_of_digit_equation (a b cin out cout : Bool)
    (h : a.toNat + b.toNat + cin.toNat =
      out.toNat + 2 * cout.toNat) :
    TuDengPivotal.majority cin a b = cout := by
  cases a <;> cases b <;> cases cin <;> cases out <;> cases cout <;>
    simp [TuDengPivotal.majority] at h ⊢

def outputWord {k : Nat} (x d : Fin k -> Bool)
    (c : Fin (k + 1) -> Bool) : Fin k -> Bool :=
  fun i => sumBit (x i) (d i) (c i.castSucc)

def encodedOutput {k : Nat} (x d : Fin k -> Bool)
    (c : Fin (k + 1) -> Bool) : Nat :=
  Nat.ofBits (outputWord x d c)

theorem selectedCarry_digit_equation {k : Nat} (x d : Fin k -> Bool)
    (i : Fin k) :
    (x i).toNat + (d i).toNat +
        (selectedCarry x d i.castSucc).toNat =
      (Nat.testBit (encodedOutput x d (selectedCarry x d)) i.val).toNat +
        2 * (selectedCarry x d i.succ).toNat := by
  rw [show Nat.testBit (encodedOutput x d (selectedCarry x d)) i.val =
      outputWord x d (selectedCarry x d) i by
    simp [encodedOutput, i.isLt]]
  rw [selectedCarry_succ]
  exact sumBit_majority_identity (x i) (d i)
    (selectedCarry x d i.castSucc)

theorem digitTrace_ext {k a b z : Nat} {q : Bool}
    {c e : Fin (k + 1) -> Bool}
    (hc0 : c 0 = q) (he0 : e 0 = q)
    (hc : forall i : Fin k,
      (Nat.testBit a i.val).toNat +
            (Nat.testBit b i.val).toNat + (c i.castSucc).toNat =
        (Nat.testBit z i.val).toNat + 2 * (c i.succ).toNat)
    (he : forall i : Fin k,
      (Nat.testBit a i.val).toNat +
            (Nat.testBit b i.val).toNat + (e i.castSucc).toNat =
        (Nat.testBit z i.val).toNat + 2 * (e i.succ).toNat) :
    c = e := by
  funext j
  induction j using Fin.induction with
  | zero => exact hc0.trans he0.symm
  | succ i ih =>
      have hci := hc i
      have hei := he i
      rw [ih] at hci
      cases hcs : c i.succ <;> cases hes : e i.succ <;>
        simp [hcs, hes] at hci hei ⊢ <;> omega

theorem selectedCarry_global_equation {k t : Nat}
    (x : Fin (2 ^ k)) (ht : t < 2 ^ k) :
    let d := targetWord k t
    let c := selectedCarry (finToWord x) d
    x.val + t + (selectedInitial (finToWord x) d).toNat =
      encodedOutput (finToWord x) d c +
        (2 ^ k) * (selectedInitial (finToWord x) d).toNat := by
  dsimp only
  let d := targetWord k t
  let c := selectedCarry (finToWord x) d
  let q := selectedInitial (finToWord x) d
  let z := encodedOutput (finToWord x) d c
  have hz : z < 2 ^ k := by
    exact Nat.ofBits_lt_two_pow (outputWord (finToWord x) d c)
  apply (tu_deng_cyclic_carry_trace_iff_sum
    k x.val t z q x.isLt ht hz).mpr
  refine ExistsUnique.intro c ?_ ?_
  · refine ⟨selectedCarry_zero _ _, ?_, ?_⟩
    · exact (selectedCarry_closed (finToWord x) d).trans
        (selectedCarry_zero (finToWord x) d)
    · intro i
      exact selectedCarry_digit_equation (finToWord x) d i
  · intro e he
    apply digitTrace_ext (c := e) (e := c) he.1 (selectedCarry_zero _ _)
      he.2.2
    intro i
    exact selectedCarry_digit_equation (finToWord x) d i

theorem selectedInitial_eq_true_iff {k t : Nat}
    (x : Fin (2 ^ k)) (ht : t < 2 ^ k) :
    selectedInitial (finToWord x) (targetWord k t) = true ↔
      2 ^ k - 1 <= x.val + t := by
  constructor
  · intro hq
    have hglobal := selectedCarry_global_equation x ht
    dsimp only at hglobal
    rw [hq] at hglobal
    simp only [Bool.toNat_true, Nat.mul_one] at hglobal
    omega
  · intro hthreshold
    let z := x.val + t + 1 - 2 ^ k
    have hpow : 1 <= 2 ^ k := Nat.one_le_pow k 2 (by decide)
    have hpowle : 2 ^ k <= x.val + t + 1 := by omega
    have hz : z < 2 ^ k := by
      dsimp [z]
      have hx := x.isLt
      omega
    have hsum : x.val + t + true.toNat = z + (2 ^ k) * true.toNat := by
      simp only [Bool.toNat_true, Nat.mul_one]
      dsimp [z]
      omega
    obtain ⟨c, hc, _⟩ :=
      (tu_deng_cyclic_carry_trace_iff_sum
        k x.val t z true x.isLt ht hz).mp hsum
    have hmajority : forall i : Fin k,
        TuDengPivotal.majority (c i.castSucc)
            (finToWord x i) (targetWord k t i) = c i.succ := by
      intro i
      apply majority_of_digit_equation
        (finToWord x i) (targetWord k t i) (c i.castSucc)
          (Nat.testBit z i.val) (c i.succ)
      simpa [finToWord, targetWord] using hc.2.2 i
    have hfrom :
        carryFrom (finToWord x) (targetWord k t) true = c :=
      carryFrom_ext hc.1 hmajority
    have hfixed :
        TuDengPivotal.propagate
          (inputTargetList (finToWord x) (targetWord k t)) true = true := by
      rw [← carryFrom_last, hfrom, hc.2.1]
    unfold selectedInitial TuDengPivotal.selectedInitial
    exact hfixed

theorem encodedOutput_eq_circularAdd {k t : Nat}
    (x : Fin (2 ^ k)) (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    let d := targetWord k t
    let c := selectedCarry (finToWord x) d
    encodedOutput (finToWord x) d c = circularAdd k x.val t := by
  dsimp only
  let d := targetWord k t
  let c := selectedCarry (finToWord x) d
  let q := selectedInitial (finToWord x) d
  let z := encodedOutput (finToWord x) d c
  change z = circularAdd k x.val t
  have hpow : 2 <= 2 ^ k := by
    have hp : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by decide)
    omega
  have htPow : t < 2 ^ k := by omega
  have htM : t < 2 ^ k - 1 := by omega
  have hglobal : x.val + t + q.toNat = z + (2 ^ k) * q.toNat :=
    selectedCarry_global_equation x htPow
  cases hq : q with
  | false =>
      have hsumlt : x.val + t < 2 ^ k - 1 := by
        have hnot : ¬ 2 ^ k - 1 <= x.val + t := by
          intro hthreshold
          have htrue :=
            (selectedInitial_eq_true_iff x htPow).mpr hthreshold
          change selectedInitial (finToWord x) (targetWord k t) = false at hq
          rw [hq] at htrue
          exact Bool.noConfusion htrue
        omega
      rw [hq] at hglobal
      simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at hglobal
      unfold circularAdd
      rw [Nat.mod_eq_of_lt hsumlt]
      exact hglobal.symm
  | true =>
      have hthreshold : 2 ^ k - 1 <= x.val + t :=
        (selectedInitial_eq_true_iff x htPow).mp hq
      rw [hq] at hglobal
      simp only [Bool.toNat_true, Nat.mul_one] at hglobal
      have hsum : x.val + t = (2 ^ k - 1) + z := by omega
      have hsumlt : x.val + t < 2 * (2 ^ k - 1) := by
        have hx := x.isLt
        omega
      have hzM : z < 2 ^ k - 1 := by omega
      unfold circularAdd
      rw [hsum, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hzM]

/-! ## Exact bad-family equivalence and cardinality -/

def carryWeight {k : Nat} (c : Fin (k + 1) -> Bool) : Nat :=
  (Finset.univ : Finset (Fin k)).sum fun i => (c i.castSucc).toNat

def IsBooleanBad {k : Nat} (x d : Fin k -> Bool) : Prop :=
  wordWeight d < carryWeight (selectedCarry x d)

@[reducible] def isBooleanBadDecidable {k : Nat} (d : Fin k -> Bool) :
    DecidablePred fun x => IsBooleanBad x d := by
  intro x
  unfold IsBooleanBad carryWeight wordWeight selectedCarry carryFrom
  infer_instance

theorem IsBooleanBad.mono {k : Nat} {x y d : Fin k -> Bool}
    (hxy : WordLE x y) (hx : IsBooleanBad x d) :
    IsBooleanBad y d := by
  unfold IsBooleanBad carryWeight at hx ⊢
  have hsum :
      (Finset.univ : Finset (Fin k)).sum
          (fun i => (selectedCarry x d i.castSucc).toNat) <=
        (Finset.univ : Finset (Fin k)).sum
          (fun i => (selectedCarry y d i.castSucc).toNat) := by
    apply Finset.sum_le_sum
    intro i hi
    have hcarry := selectedCarry_mono (d := d) hxy i.castSucc
    cases hxi : selectedCarry x d i.castSucc with
    | false => simp
    | true =>
        have hyi : selectedCarry y d i.castSucc = true := by
          cases hy : selectedCarry y d i.castSucc with
          | false =>
              exfalso
              exact (by decide : ¬ (true <= false)) (by simpa [hxi, hy] using hcarry)
          | true => rfl
        simp [hyi]
  omega

theorem selectedCarry_weight_identity {k t : Nat}
    (x : Fin (2 ^ k)) (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    let d := targetWord k t
    let c := selectedCarry (finToWord x) d
    binaryWeightUpTo k x.val + binaryWeightUpTo k t =
      binaryWeightUpTo k (circularAdd k x.val t) + carryWeight c := by
  dsimp only
  let d := targetWord k t
  let c := selectedCarry (finToWord x) d
  let z := encodedOutput (finToWord x) d c
  have hcycle : c 0 = c (Fin.last k) :=
    (selectedCarry_closed (finToWord x) d).symm
  have hstep : forall i : Fin k,
      (Nat.testBit x.val i.val).toNat +
            (Nat.testBit t i.val).toNat + (c i.castSucc).toNat =
        (Nat.testBit z i.val).toNat + 2 * (c i.succ).toNat := by
    intro i
    exact selectedCarry_digit_equation (finToWord x) d i
  have hweight :=
    (tu_deng_cyclic_carry_weight_identity
      k x.val t z c hcycle hstep).1
  dsimp only at hweight
  rw [← endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum
        k x.val,
      ← endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum
        k t,
      ← endpoint_deficit_cases_round_2_tu_deng_binary_weight_up_to_eq_fin_testbit_sum
        k z] at hweight
  have hzEq : z = circularAdd k x.val t :=
    encodedOutput_eq_circularAdd x hk ht
  rw [hzEq] at hweight
  change binaryWeightUpTo k x.val + binaryWeightUpTo k t =
    binaryWeightUpTo k (circularAdd k x.val t) + carryWeight c
  exact hweight

theorem circularDecrease_iff_booleanBad {k t : Nat}
    (x : Fin (2 ^ k)) (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    circularDecrease k t x.val ↔
      IsBooleanBad (finToWord x) (targetWord k t) := by
  have hweight := selectedCarry_weight_identity x hk ht
  dsimp only at hweight
  unfold circularDecrease IsBooleanBad
  rw [wordWeight_targetWord]
  omega

def booleanBadFamily (k t : Nat) : Finset (Fin k -> Bool) :=
  letI : DecidablePred (fun x => IsBooleanBad x (targetWord k t)) :=
    isBooleanBadDecidable (targetWord k t)
  (Finset.univ : Finset (Fin k -> Bool)).filter fun x =>
      IsBooleanBad x (targetWord k t)

theorem circularDecreaseCount_eq_booleanBadFamily_card
    {k t : Nat} (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    circularDecreaseCount k t = (booleanBadFamily k t).card := by
  classical
  letI : DecidablePred (circularDecrease k t) :=
    circularDecreaseDecidable k t
  letI : DecidablePred (fun x => IsBooleanBad x (targetWord k t)) :=
    isBooleanBadDecidable (targetWord k t)
  let numericFamily :=
    (Finset.univ : Finset (Fin (2 ^ k))).filter fun x =>
      circularDecrease k t x.val
  have hnumeric : circularDecreaseCount k t = numericFamily.card := by
    unfold circularDecreaseCount
    apply Finset.card_bij
      (fun n hn => (⟨n, (Finset.mem_range.mp
        (Finset.mem_filter.mp hn).1)⟩ : Fin (2 ^ k)))
    · intro n hn
      simp only [numericFamily, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hn).2
    · intro a ha b hb hab
      exact Fin.ext_iff.mp hab
    · intro x hx
      refine ⟨x.val, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr x.isLt,
          (Finset.mem_filter.mp hx).2⟩
      · exact Fin.ext rfl
  rw [hnumeric]
  apply Finset.card_equiv (bitWordEquiv k)
  intro x
  simp only [numericFamily, booleanBadFamily, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact circularDecrease_iff_booleanBad x hk ht

theorem tuDengCount_eq_booleanBadFamily_card
    {k t : Nat} (hk : 2 <= k) (htPos : 1 <= t)
    (ht : t <= 2 ^ k - 2) :
    tuDengCount k t = (booleanBadFamily k t).card := by
  rw [tuDeng_pair_count_eq_circular_decrease_count hk htPos ht,
    circularDecreaseCount_eq_booleanBadFamily_card (by omega) ht]

/-! ## The exceptional input `1 - d` -/

def exceptionalWord {k : Nat} (d : Fin k -> Bool) : Fin k -> Bool :=
  fun i => !(d i)

theorem selectedCarry_exceptional {k : Nat} (d : Fin k -> Bool) :
    selectedCarry (exceptionalWord d) d = fun _ => true := by
  have hstep : forall i : Fin k,
      TuDengPivotal.majority true (exceptionalWord d i) (d i) = true := by
    intro i
    cases hdi : d i <;> simp [exceptionalWord, hdi, TuDengPivotal.majority]
  have hfrom : carryFrom (exceptionalWord d) d true = fun _ => true :=
    carryFrom_ext rfl hstep
  have hfixed :
      TuDengPivotal.propagate (inputTargetList (exceptionalWord d) d) true =
        true := by
    rw [← carryFrom_last, hfrom]
  have hselected : selectedInitial (exceptionalWord d) d = true := by
    unfold selectedInitial TuDengPivotal.selectedInitial
    exact hfixed
  unfold selectedCarry
  rw [hselected]
  exact hfrom

def complementRepresentative (k t : Nat) (ht : t < 2 ^ k) : Fin (2 ^ k) :=
  ⟨2 ^ k - 1 - t, by omega⟩

theorem finToWord_complementRepresentative (k t : Nat) (ht : t < 2 ^ k) :
    finToWord (complementRepresentative k t ht) =
      exceptionalWord (targetWord k t) := by
  funext i
  exact tu_deng_low_bit_complement_below_pow k t ht i

theorem wordToFin_exceptionalWord (k t : Nat) (ht : t < 2 ^ k) :
    wordToFin (exceptionalWord (targetWord k t)) =
      complementRepresentative k t ht := by
  apply (bitWordEquiv k).injective
  change finToWord (wordToFin (exceptionalWord (targetWord k t))) =
    finToWord (complementRepresentative k t ht)
  rw [finToWord_wordToFin, finToWord_complementRepresentative]

theorem binaryWeightUpTo_pos_of_pos {k n : Nat}
    (hnPos : 0 < n) (hn : n < 2 ^ k) :
    0 < binaryWeightUpTo k n := by
  induction k generalizing n with
  | zero =>
      simp only [pow_zero] at hn
      omega
  | succ k ih =>
      rw [binaryWeightUpTo_succ_div_two]
      have hmod : n % 2 < 2 := Nat.mod_lt n (by omega)
      by_cases hz : n % 2 = 0
      · have hdivPos : 0 < n / 2 := by
          have hdecomp := Nat.mod_add_div n 2
          omega
        have hdivLt : n / 2 < 2 ^ k := by
          rw [Nat.pow_succ] at hn
          omega
        have hrec := ih hdivPos hdivLt
        omega
      · omega

theorem exceptionalWord_isBooleanBad {k t : Nat}
    (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    IsBooleanBad (exceptionalWord (targetWord k t)) (targetWord k t) := by
  have hpow : 2 <= 2 ^ k := by
    have hp : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hcompPos :
      0 < binaryWeightUpTo k (2 ^ k - 1 - t) := by
    apply binaryWeightUpTo_pos_of_pos
    · omega
    · omega
  have hcomplement := binaryWeightUpTo_complement (k := k) (n := t) (by omega)
  have htarget : binaryWeightUpTo k t < k := by omega
  unfold IsBooleanBad
  rw [wordWeight_targetWord, selectedCarry_exceptional]
  simpa [carryWeight] using htarget

theorem exceptionalWord_mem_booleanBadFamily {k t : Nat}
    (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    exceptionalWord (targetWord k t) ∈ booleanBadFamily k t := by
  classical
  simp only [booleanBadFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exceptionalWord_isBooleanBad hk ht

/-! ## Reindexing the cube by `ZMod k` -/

def finZModWordEquiv (k : Nat) [NeZero k] :
    (Fin k -> Bool) ≃ (ZMod k -> Bool) :=
  Equiv.arrowCongr (ZMod.finEquiv k).toEquiv (Equiv.refl Bool)

def zmodTargetWord (k t : Nat) [NeZero k] : ZMod k -> Bool :=
  finZModWordEquiv k (targetWord k t)

theorem zmodTargetWord_apply (k t : Nat) [NeZero k] (i : ZMod k) :
    zmodTargetWord k t i = Nat.testBit t i.val := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => rfl

def IsZModBooleanBad (k t : Nat) [NeZero k] (x : ZMod k -> Bool) : Prop :=
  IsBooleanBad ((finZModWordEquiv k).symm x) (targetWord k t)

@[reducible] def isZModBooleanBadDecidable (k t : Nat) [NeZero k] :
    DecidablePred (IsZModBooleanBad k t) := by
  intro x
  unfold IsZModBooleanBad
  exact isBooleanBadDecidable (targetWord k t) _

def zmodBooleanBadFamily (k t : Nat) [NeZero k] :
    Finset (ZMod k -> Bool) :=
  letI : DecidablePred (IsZModBooleanBad k t) :=
    isZModBooleanBadDecidable k t
  (Finset.univ : Finset (ZMod k -> Bool)).filter (IsZModBooleanBad k t)

theorem booleanBadFamily_card_eq_zmodBooleanBadFamily_card
    (k t : Nat) [NeZero k] :
    (booleanBadFamily k t).card = (zmodBooleanBadFamily k t).card := by
  classical
  letI : DecidablePred (fun x => IsBooleanBad x (targetWord k t)) :=
    isBooleanBadDecidable (targetWord k t)
  letI : DecidablePred (IsZModBooleanBad k t) :=
    isZModBooleanBadDecidable k t
  apply Finset.card_equiv (finZModWordEquiv k)
  intro x
  simp only [booleanBadFamily, zmodBooleanBadFamily, Finset.mem_filter,
    Finset.mem_univ, true_and, IsZModBooleanBad, Equiv.symm_apply_apply]

theorem circularDecreaseCount_eq_zmodBooleanBadFamily_card
    {k t : Nat} [NeZero k] (hk : 1 <= k) (ht : t <= 2 ^ k - 2) :
    circularDecreaseCount k t = (zmodBooleanBadFamily k t).card := by
  rw [circularDecreaseCount_eq_booleanBadFamily_card hk ht,
    booleanBadFamily_card_eq_zmodBooleanBadFamily_card]

theorem tuDengCount_eq_zmodBooleanBadFamily_card
    {k t : Nat} [NeZero k] (hk : 2 <= k) (htPos : 1 <= t)
    (ht : t <= 2 ^ k - 2) :
    tuDengCount k t = (zmodBooleanBadFamily k t).card := by
  rw [tuDengCount_eq_booleanBadFamily_card hk htPos ht,
    booleanBadFamily_card_eq_zmodBooleanBadFamily_card]

end LeanCipher.TuDengBooleanBridge

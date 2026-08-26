import Mathlib

open Set MeasureTheory
open scoped intervalIntegral

namespace TuDengPivotal

/-!
The carry interface uses the paper's `Fin (k + 1)` convention: the two
endpoints are the incoming carry before bit `0` and after bit `k - 1`.
`carryCompatible` is the exact local majority recurrence, while
`carryCompatible_iff` exposes the supported-path condition (3) and (P6): a
matching state forces the next carry to agree and a mismatch fixes the input
bit to the next carry.  This is independent of the global root argument.

The list model below constructs the greatest closed carry path and proves its
coordinatewise monotonicity when the input word increases at a fixed target.
The file also checks the numerical profile balance (P7)--(P9) and the complete
real-integral inequality (P10).  It does not yet bridge the list-selected path
to the `Fin` compatibility interface, prove that two selected paths differ on
one cyclic interval (P4)--(P5), or perform the pivotal-edge partition/Russo
sum in (P11).  Those are the remaining interfaces needed to turn this block
into an alternative proof of the uniform half-bound.
-/

def majority (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

def carryCompatible {k : Nat}
    (x d : Fin k -> Bool) (c : Fin (k + 1) -> Bool) : Prop :=
  ∀ i : Fin k,
    majority (c i.castSucc) (x i) (d i) = c i.succ

theorem majority_eq_iff (a b c y : Bool) :
    majority a b c = y ↔
      (a = c ∧ y = a) ∨ (a ≠ c ∧ b = y) := by
  cases a <;> cases b <;> cases c <;> cases y <;>
    simp [majority]

theorem majority_eq_of_eq_left_right {a b : Bool} :
    majority a b a = a := by
  cases a <;> cases b <;> rfl

theorem majority_eq_middle_of_ne {a b c : Bool} (h : a ≠ c) :
    majority a b c = b := by
  have := (majority_eq_iff a b c b).mpr (Or.inr ⟨h, rfl⟩)
  exact this

theorem majority_mono_input {a b b' c : Bool} (h : b <= b') :
    majority a b c <= majority a b' c := by
  cases a <;> cases b <;> cases b' <;> cases c <;>
    simp [majority] at * <;> omega

theorem majority_mono_carry {a a' b c : Bool} (h : a <= a') :
    majority a b c <= majority a' b c := by
  cases a <;> cases a' <;> cases b <;> cases c <;>
    simp [majority] at * <;> omega

theorem majority_mono {a a' b b' c : Bool}
    (ha : a <= a') (hb : b <= b') :
    majority a b c <= majority a' b' c := by
  exact (majority_mono_carry ha).trans (majority_mono_input hb)

def gate (state : Bool) (inputTarget : Bool × Bool) : Bool :=
  majority state inputTarget.1 inputTarget.2

def SameTargetInputLE (left right : Bool × Bool) : Prop :=
  left.2 = right.2 ∧ left.1 <= right.1

def propagate (word : List (Bool × Bool)) (initial : Bool) : Bool :=
  word.foldl gate initial

def carryPath (word : List (Bool × Bool)) (initial : Bool) : List Bool :=
  word.scanl gate initial

theorem gate_mono {state state' : Bool} {left right : Bool × Bool}
    (hstate : state <= state') (hword : SameTargetInputLE left right) :
    gate state left <= gate state' right := by
  rcases left with ⟨input, target⟩
  rcases right with ⟨input', target'⟩
  simp only [SameTargetInputLE] at hword
  rcases hword with ⟨htarget, hinput⟩
  subst target'
  exact majority_mono hstate hinput

theorem propagate_mono
    {left right : List (Bool × Bool)}
    (hword : List.Forall₂ SameTargetInputLE left right)
    {initial initial' : Bool} (hinitial : initial <= initial') :
    propagate left initial <= propagate right initial' := by
  induction hword generalizing initial initial' with
  | nil => simpa [propagate] using hinitial
  | cons hgate htail ih =>
      simpa [propagate] using ih (gate_mono hinitial hgate)

theorem carryPath_mono
    {left right : List (Bool × Bool)}
    (hword : List.Forall₂ SameTargetInputLE left right)
    {initial initial' : Bool} (hinitial : initial <= initial') :
    List.Forall₂ (fun x y : Bool => x <= y)
      (carryPath left initial) (carryPath right initial') := by
  induction hword generalizing initial initial' with
  | nil =>
      simpa [carryPath] using
        (List.Forall₂.cons hinitial (List.Forall₂.nil))
  | cons hgate htail ih =>
      simpa [carryPath] using
        (List.Forall₂.cons hinitial (ih (gate_mono hinitial hgate)))

def selectedInitial (word : List (Bool × Bool)) : Bool :=
  propagate word true

def selectedCarryPath (word : List (Bool × Bool)) : List Bool :=
  carryPath word (selectedInitial word)

theorem selectedInitial_fixed (word : List (Bool × Bool)) :
    propagate word (selectedInitial word) = selectedInitial word := by
  cases htop : propagate word true with
  | true => simp [selectedInitial, htop]
  | false =>
      have hmono : propagate word false <= propagate word true :=
        propagate_mono
          (List.forall₂_same.mpr (fun _ _ => ⟨rfl, le_rfl⟩)) (by decide)
      rw [htop] at hmono
      have hbottom : propagate word false = false := by
        cases h : propagate word false
        · rfl
        · rw [h] at hmono
          exact ((by decide : ¬ (true <= false)) hmono).elim
      simp [selectedInitial, htop, hbottom]

theorem fixed_initial_le_selected {word : List (Bool × Bool)} {initial : Bool}
    (hfixed : propagate word initial = initial) :
    initial <= selectedInitial word := by
  cases initial with
  | false => exact Bool.false_le _
  | true => simp [selectedInitial, hfixed]

theorem selectedInitial_is_greatest_fixed (word : List (Bool × Bool)) :
    propagate word (selectedInitial word) = selectedInitial word ∧
      ∀ initial : Bool, propagate word initial = initial ->
        initial <= selectedInitial word := by
  exact ⟨selectedInitial_fixed word,
    fun _ hfixed => fixed_initial_le_selected hfixed⟩

theorem selectedCarryPath_head? (word : List (Bool × Bool)) :
    (selectedCarryPath word).head? = some (selectedInitial word) := by
  exact List.head?_scanl

theorem selectedCarryPath_last? (word : List (Bool × Bool)) :
    (selectedCarryPath word).getLast? = some (selectedInitial word) := by
  rw [selectedCarryPath, carryPath, List.getLast?_scanl]
  change some (propagate word (selectedInitial word)) = _
  rw [selectedInitial_fixed]

theorem selectedCarryPath_closed (word : List (Bool × Bool)) :
    (selectedCarryPath word).head? = (selectedCarryPath word).getLast? := by
  rw [selectedCarryPath_head?, selectedCarryPath_last?]

theorem selectedCarryPath_mono
    {left right : List (Bool × Bool)}
    (hword : List.Forall₂ SameTargetInputLE left right) :
    List.Forall₂ (fun x y : Bool => x <= y)
      (selectedCarryPath left) (selectedCarryPath right) := by
  apply carryPath_mono hword
  exact propagate_mono hword (le_refl true)

theorem carryCompatible_iff {k : Nat}
    (x d : Fin k -> Bool) (c : Fin (k + 1) -> Bool) :
    carryCompatible x d c ↔
      (∀ i : Fin k, c i.castSucc = d i -> c i.succ = c i.castSucc) ∧
      (∀ i : Fin k, c i.castSucc ≠ d i -> x i = c i.succ) := by
  constructor
  · intro h
    constructor
    · intro i hmatch
      have hg := (majority_eq_iff (c i.castSucc) (x i) (d i) (c i.succ)).mp (h i)
      rcases hg with ⟨_, hnext⟩ | ⟨hne, _⟩
      · exact hnext
      · exact (hne hmatch).elim
    · intro i hmis
      have hg := (majority_eq_iff (c i.castSucc) (x i) (d i) (c i.succ)).mp (h i)
      rcases hg with ⟨heq, _⟩ | ⟨_, hx⟩
      · exact (hmis heq).elim
      · exact hx
  · rintro ⟨hmatch, hmis⟩ i
    apply (majority_eq_iff (c i.castSucc) (x i) (d i) (c i.succ)).mpr
    by_cases hi : c i.castSucc = d i
    · exact Or.inl ⟨hi, hmatch i hi⟩
    · exact Or.inr ⟨hi, hmis i hi⟩

theorem carryCompatible_implies_support {k : Nat}
    {x d : Fin k -> Bool} {c : Fin (k + 1) -> Bool}
    (h : carryCompatible x d c) :
    ∀ i : Fin k, c i.castSucc = d i -> c i.succ = c i.castSucc := by
  exact (carryCompatible_iff x d c).mp h |>.1

theorem carryCompatible_mismatch_forces_input {k : Nat}
    {x d : Fin k -> Bool} {c : Fin (k + 1) -> Bool}
    (h : carryCompatible x d c) :
    ∀ i : Fin k, c i.castSucc ≠ d i -> x i = c i.succ := by
  exact (carryCompatible_iff x d c).mp h |>.2

/- The numerical content of (P7)--(P9): once the fixed-bit counts are
  `a = R - 1` and `b = |U| - R + p0`, the cyclic telescoping identity
  `2R - |U| = h` gives the nonnegative bias `a - b = h - 1 - p0`. -/
theorem pivotal_profile_balance
    (h u r p0 : Nat)
    (hTel : 2 * r = u + h)
    (hr : 1 <= r)
    (hh : 1 <= h)
    (hru : r <= u)
    (hp0 : p0 <= h - 1) :
    (r - 1) - (u - r + p0) = h - 1 - p0 /\
      u - r + p0 <= r - 1 := by
  constructor
  · omega
  · have hur : u - r = r - h := by omega
    have hhr : h <= r := by omega
    rw [hur]
    calc
      r - h + p0 <= r - h + (h - 1) := Nat.add_le_add_left hp0 (r - h)
      _ = r - 1 := by omega

theorem biased_integrand_nonneg
    {a b : Nat} (hab : b <= a) {p : ℝ} (hp : p ∈ Set.Icc 0 (1 / 2)) :
    0 <= (1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b := by
  have hp0 : 0 <= p := hp.1
  have hhalf : p <= 1 / 2 := hp.2
  have hcomp : p <= 1 - p := by linarith
  have h1p : 0 <= 1 - p := by linarith
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  have hpow : p ^ d <= (1 - p) ^ d := by
    exact pow_le_pow_left₀ hp0 hcomp d
  have hcommon : 0 <= (1 - p) ^ b * p ^ b := by
    exact mul_nonneg (pow_nonneg h1p b) (pow_nonneg hp0 b)
  have hmul :
      (1 - p) ^ b * p ^ b * p ^ d <=
        (1 - p) ^ b * p ^ b * (1 - p) ^ d := by
    exact mul_le_mul_of_nonneg_left hpow hcommon
  have hleft :
      p ^ a * (1 - p) ^ b =
        (1 - p) ^ b * p ^ b * p ^ d := by
    rw [hd, pow_add]
    ring
  have hright :
      (1 - p) ^ b * p ^ b * (1 - p) ^ d =
        (1 - p) ^ a * p ^ b := by
    rw [hd, pow_add]
    ring
  rw [sub_nonneg]
  rw [hleft, ← hright]
  exact hmul

theorem biased_integral_nonneg (a b : Nat) (hab : b <= a) :
    0 <= ∫ p : ℝ in (0 : ℝ)..(1 / 2),
      ((1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b) := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro p hp
  exact biased_integrand_nonneg hab hp

end TuDengPivotal

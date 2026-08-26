import Mathlib

open scoped BigOperators

namespace VectorialNonlinearity

/-!
The paper's critical case has `q = 2^k` with `k >= 3`, hence `q = 8*r` for
`r = 2^(k-3)`.  The finite types below stand for the output indices,
frequency indices, and fibres.  Their cardinalities are hypotheses in the
arithmetic interface so that this file stays independent of a choice of
coordinates for `F_2^n`; the standard coordinate cardinality is checked by
`f2VecCard`.

The three declarations below formalize the contradiction chain behind
Lemmas 5.3 and 5.4 of the submission.  They do not claim that the Walsh
inversion, Parseval, or maximal-bent-fibre identities have already been
formalized here: those identities are named hypotheses of
`criticalCosetContradiction`.  Every declaration in this file is kernel
checked; none uses an unproved admission or an opaque replacement for one of
those identities.
-/

theorem f2VecCard (n : Nat) :
    Fintype.card (Fin n -> ZMod 2) = 2 ^ n := by
  simp

theorem powTwo_eq_eight_mul (k : Nat) (hk : 3 <= k) :
    exists r : Nat, 2 ^ k = 8 * r := by
  refine ⟨2 ^ (k - 3), ?_⟩
  rw [show k = 3 + (k - 3) by omega, pow_add]
  norm_num

theorem forcedTwoLevelOfRowMoments
    {A : Type*} [Fintype A]
    (q r : Nat) (hq : q = 8 * r) (hr : 0 < r)
    (hcardA : Fintype.card A = q ^ 2)
    (c : A -> Int)
    (hBound : forall a, |c a| <= (r : Int))
    (hRow :
      2 * (Finset.univ.sum fun a : A => 1 + 4 * c a) = (q : Int) ^ 2 \/
      2 * (Finset.univ.sum fun a : A => 1 + 4 * c a) = -((q : Int) ^ 2))
    (hParseval :
      4 * (Finset.univ.sum fun a : A => (1 + 4 * c a) ^ 2) =
        (q : Int) ^ 4) :
    forall a,
      |2 * (1 + 4 * c a)| = (q : Int) - 2 \/
      |2 * (1 + 4 * c a)| = (q : Int) + 2 := by
  subst q
  have hrInt : (0 : Int) < r := by exact_mod_cast hr
  let C : Int := Finset.univ.sum fun a : A => c a
  let S : Int := Finset.univ.sum fun a : A => c a ^ 2
  have hCardCast : (Fintype.card A : Int) = ((8 * r : Nat) : Int) ^ 2 := by
    exact_mod_cast hcardA
  have hLinearSum :
      (Finset.univ.sum fun a : A => 1 + 4 * c a) =
        ((8 * r : Nat) : Int) ^ 2 + 4 * C := by
    dsimp [C]
    calc
      (Finset.univ.sum fun a : A => 1 + 4 * c a) =
          (Fintype.card A : Int) + 4 * (Finset.univ.sum fun a : A => c a) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ((8 * r : Nat) : Int) ^ 2 +
          4 * (Finset.univ.sum fun a : A => c a) := by rw [hCardCast]
  have hSquareSum :
      (Finset.univ.sum fun a : A => (1 + 4 * c a) ^ 2) =
        ((8 * r : Nat) : Int) ^ 2 + 8 * C + 16 * S := by
    dsimp [C, S]
    calc
      (Finset.univ.sum fun a : A => (1 + 4 * c a) ^ 2) =
          Finset.univ.sum (fun a : A => 1 + 8 * c a + 16 * c a ^ 2) := by
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = (Fintype.card A : Int) +
          8 * (Finset.univ.sum fun a : A => c a) +
          16 * (Finset.univ.sum fun a : A => c a ^ 2) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ((8 * r : Nat) : Int) ^ 2 +
          8 * (Finset.univ.sum fun a : A => c a) +
          16 * (Finset.univ.sum fun a : A => c a ^ 2) := by rw [hCardCast]
  have hEachSquare (a : A) : c a ^ 2 <= (r : Int) ^ 2 := by
    have habs := hBound a
    have habsnonneg := abs_nonneg (c a)
    nlinarith [sq_abs (c a)]
  have hSumBound : S <= ((8 * r : Nat) : Int) ^ 2 * (r : Int) ^ 2 := by
    dsimp [S]
    calc
      (Finset.univ.sum fun a : A => c a ^ 2) <=
          Finset.univ.sum (fun _a : A => (r : Int) ^ 2) := by
            exact Finset.sum_le_sum fun a _ => hEachSquare a
      _ = (Fintype.card A : Int) * (r : Int) ^ 2 := by simp
      _ = ((8 * r : Nat) : Int) ^ 2 * (r : Int) ^ 2 := by rw [hCardCast]
  rcases hRow with hPositive | hNegative
  · rw [hLinearSum] at hPositive
    rw [hSquareSum] at hParseval
    have hC : C = -8 * (r : Int) ^ 2 := by
      norm_num at hPositive
      nlinarith
    have hS : S = ((8 * r : Nat) : Int) ^ 2 * (r : Int) ^ 2 := by
      norm_num at hParseval
      rw [hC] at hParseval
      nlinarith
    have hAllSquares : forall a : A, c a ^ 2 = (r : Int) ^ 2 := by
      have hSumEquality :
          (Finset.univ.sum fun a : A => c a ^ 2) =
            Finset.univ.sum (fun _a : A => (r : Int) ^ 2) := by
        dsimp [S] at hS
        calc
          (Finset.univ.sum fun a : A => c a ^ 2) =
              ((8 * r : Nat) : Int) ^ 2 * (r : Int) ^ 2 := hS
          _ = (Fintype.card A : Int) * (r : Int) ^ 2 := by rw [hCardCast]
          _ = Finset.univ.sum (fun _a : A => (r : Int) ^ 2) := by simp
      have hPointwise :=
        (Finset.sum_eq_sum_iff_of_le
          (s := (Finset.univ : Finset A))
          (f := fun a : A => c a ^ 2)
          (g := fun _a : A => (r : Int) ^ 2)
          (fun a _ => hEachSquare a)).mp hSumEquality
      intro a
      exact hPointwise a (Finset.mem_univ a)
    intro a
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (hAllSquares a)) with hc | hc
    · right
      rw [hc, abs_of_nonneg]
      · push_cast
        ring
      · positivity
    · left
      rw [hc, abs_of_nonpos]
      · push_cast
        ring
      · norm_num
        omega
  · rw [hLinearSum] at hNegative
    rw [hSquareSum] at hParseval
    have hC : C = -24 * (r : Int) ^ 2 := by
      norm_num at hNegative
      nlinarith
    rw [hC] at hParseval
    norm_num at hParseval hSumBound
    nlinarith

theorem oddFibresExcludeTwoLevel
    {U Y : Type*} [Fintype U] [Fintype Y]
    (q r : Nat) (hq : q = 8 * r) (hr : 0 < r)
    (hcardU : Fintype.card U = q) (hcardY : Fintype.card Y = q)
    (z : U -> Int) (T : Y -> Int)
    (hOdd : forall y, Odd (T y))
    (hParseval :
      4 * (Finset.univ.sum fun u : U => z u ^ 2) =
        (q : Int) * (Finset.univ.sum fun y : Y => T y ^ 2))
    (hTwoLevel : forall u,
      |2 * z u| = (q : Int) - 2 \/ |2 * z u| = (q : Int) + 2) :
    False := by
  subst q
  have hqpos : (0 : Int) < (8 * r : Nat) := by exact_mod_cast (by omega : 0 < 8 * r)
  choose fibreQuotient hFibreQuotient using fun y =>
    (Int.eight_dvd_sq_sub_one_of_odd (hOdd y))
  have hTSquare (y : Y) :
      T y ^ 2 = 1 + 8 * fibreQuotient y := by
    have hy := hFibreQuotient y
    omega
  have hTSum :
      (Finset.univ.sum fun y : Y => T y ^ 2) =
        (8 * r : Nat) + 8 * (Finset.univ.sum fun y : Y => fibreQuotient y) := by
    calc
      (Finset.univ.sum fun y : Y => T y ^ 2) =
          Finset.univ.sum (fun y : Y => (1 : Int) + 8 * fibreQuotient y) := by
            apply Finset.sum_congr rfl
            intro y _
            exact hTSquare y
      _ = (Fintype.card Y : Int) +
          8 * (Finset.univ.sum fun y : Y => fibreQuotient y) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (8 * r : Nat) +
          8 * (Finset.univ.sum fun y : Y => fibreQuotient y) := by
            rw [hcardY]
  have hZDivisible : exists D : Int,
      (Finset.univ.sum fun u : U => z u ^ 2) =
        2 * (8 * r : Nat) * D := by
    refine ⟨r + (Finset.univ.sum fun y : Y => fibreQuotient y), ?_⟩
    rw [hTSum] at hParseval
    norm_num at hParseval ⊢
    nlinarith
  have hEach (u : U) : exists d : Int,
      z u ^ 2 = 2 * (8 * r : Nat) * d + (8 * r : Nat) + 1 := by
    rcases hTwoLevel u with hminus | hplus
    · refine ⟨(r : Int) - 1, ?_⟩
      have hsquare := congrArg (fun x : Int => x ^ 2) hminus
      dsimp at hsquare
      rw [sq_abs] at hsquare
      norm_num at hsquare ⊢
      nlinarith
    · refine ⟨r, ?_⟩
      have hsquare := congrArg (fun x : Int => x ^ 2) hplus
      dsimp at hsquare
      rw [sq_abs] at hsquare
      norm_num at hsquare ⊢
      nlinarith
  choose d hd using hEach
  have hZNonzero : exists D : Int,
      (Finset.univ.sum fun u : U => z u ^ 2) =
        2 * (8 * r : Nat) * D + (8 * r : Nat) := by
    refine ⟨(Finset.univ.sum fun u : U => d u) + 4 * r, ?_⟩
    calc
      (Finset.univ.sum fun u : U => z u ^ 2) =
          Finset.univ.sum (fun u : U =>
            2 * (8 * r : Nat) * d u + (8 * r : Nat) + 1) := by
              apply Finset.sum_congr rfl
              intro u _
              exact hd u
      _ = 2 * (8 * r : Nat) * (Finset.univ.sum fun u : U => d u) +
          (Fintype.card U : Int) * ((8 * r : Nat) + 1) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
            ring
      _ = 2 * (8 * r : Nat) *
          ((Finset.univ.sum fun u : U => d u) + 4 * r) + (8 * r : Nat) := by
            rw [hcardU]
            norm_num
            ring
  rcases hZDivisible with ⟨D0, hD0⟩
  rcases hZNonzero with ⟨D1, hD1⟩
  rw [hD0] at hD1
  have hfactor : (8 * r : Nat) * (2 * D0 - 2 * D1 - 1) = 0 := by
    linear_combination hD1
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · exact (ne_of_gt hqpos) hzero
  · omega

/-!
`criticalCosetContradiction` is the abstracted contradiction chain in the
critical case `m = k + 1`.  The row hypotheses are exactly the identities
used in Lemma 5.3, and the column hypothesis is the Hadamard/Parseval identity
used in Lemma 5.4.  The source of these identities (Walsh inversion and the
odd maximal-bent fibres) is deliberately a hypothesis boundary here; the
arithmetic implication itself is checked below without axioms.
-/
theorem criticalCosetContradiction
    {U A Y : Type*} [Fintype U] [Fintype A] [Fintype Y]
    (q r : Nat) (hq : q = 8 * r) (hr : 0 < r)
    (hcardU : Fintype.card U = q) (hcardA : Fintype.card A = q ^ 2)
    (hcardY : Fintype.card Y = q)
    (c : U -> A -> Int) (T : A -> Y -> Int)
    (hBound : forall u a, |c u a| <= (r : Int))
    (hRow : forall u,
      2 * (Finset.univ.sum fun a : A => 1 + 4 * c u a) = (q : Int) ^ 2 \/
      2 * (Finset.univ.sum fun a : A => 1 + 4 * c u a) = -((q : Int) ^ 2))
    (hRowParseval : forall u,
      4 * (Finset.univ.sum fun a : A => (1 + 4 * c u a) ^ 2) =
        (q : Int) ^ 4)
    (hOddFibres : forall a y, Odd (T a y))
    (hColumnParseval : forall a,
      4 * (Finset.univ.sum fun u : U => (1 + 4 * c u a) ^ 2) =
        (q : Int) * (Finset.univ.sum fun y : Y => T a y ^ 2)) :
    False := by
  have hTwoLevel : forall u a,
      |2 * (1 + 4 * c u a)| = (q : Int) - 2 \/
      |2 * (1 + 4 * c u a)| = (q : Int) + 2 := by
    intro u
    exact forcedTwoLevelOfRowMoments q r hq hr hcardA (c u)
      (fun a => hBound u a) (hRow u) (hRowParseval u)
  have hqpos : 0 < q := by rw [hq]; omega
  have hApos : 0 < Fintype.card A := by
    rw [hcardA]
    nlinarith
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hApos
  exact oddFibresExcludeTwoLevel q r hq hr hcardU hcardY
    (fun u : U => 1 + 4 * c u a) (T a)
    (fun y => hOddFibres a y) (hColumnParseval a)
    (fun u => hTwoLevel u a)

end VectorialNonlinearity

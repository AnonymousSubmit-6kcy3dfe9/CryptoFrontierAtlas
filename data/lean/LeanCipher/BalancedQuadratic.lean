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
import LeanCipher.SymmetricBoolean
import LeanCipher.F2
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
This file contains mechanically assembled quadratic-form lemmas. It has been
normalized for publication and is checked with Lean's default binder-annotation
validation enabled. All declarations are checked by the Lean kernel; the file
contains no generated axiom or admitted theorem.
-/

namespace LeanCipher.GeneratedVerifiedLemmas


open LeanCipher









theorem card_product_subtype_eq_sum_fiber_subtypes
    (α β : Type*) [Fintype α] [Fintype β]
    (P : α → β → Prop) [DecidablePred (fun p : α × β => P p.1 p.2)]
    [∀ a : α, DecidablePred (fun b : β => P a b)] :
    Fintype.card {p : α × β // P p.1 p.2} =
      Finset.univ.sum (fun a : α => Fintype.card {b : β // P a b}) := by
  classical
    let e : {p : α × β // P p.1 p.2} ≃ Sigma (fun a : α => {b : β // P a b}) :=
      { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
        invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
        left_inv := by
          intro p
          cases p with
          | mk p hp =>
            cases p
            rfl
        right_inv := by
          intro s
          cases s with
          | mk a b =>
            cases b
            rfl }
    rw [Fintype.card_congr e]
    exact Fintype.card_sigma


theorem upper_triangular_nonzero_balanced_affine_param_card_eq_sum_fibers_q2
    (n : ℕ) :
    (let Quad :=
      (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let AffineParam := (Fin n → ZMod 2) × ZMod 2;
     let BalancedAffineParam : Quad → AffineParam → Prop := fun Q b =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0)
        then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0;
     Fintype.card
       {p : {Q : Quad // Q ≠ 0} × AffineParam //
         BalancedAffineParam p.1.1 p.2}
      =
     Finset.univ.sum (fun Q : {Q : Quad // Q ≠ 0} =>
       Fintype.card {b : AffineParam // BalancedAffineParam Q.1 b})) := by
  classical
  let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2
  let AffineParam := (Fin n → ZMod 2) × ZMod 2
  let BalancedAffineParam : Quad → AffineParam → Prop := fun Q b =>
    Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if
        (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            Q i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0)
      then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0
  change
    Fintype.card
        {p : {Q : Quad // Q ≠ 0} × AffineParam //
          BalancedAffineParam p.1.1 p.2} =
      Finset.univ.sum (fun Q : {Q : Quad // Q ≠ 0} =>
        Fintype.card {b : AffineParam // BalancedAffineParam Q.1 b})
  exact card_product_subtype_eq_sum_fiber_subtypes
    ({Q : Quad // Q ≠ 0}) AffineParam (fun Q b => BalancedAffineParam Q.1 b)


































theorem radicalLinear_nonzero_walshSum_eq_zero
    {α : Type*} [Fintype α]
    (k : ℕ) (g : α → ZMod 2) (c : Fin k → ZMod 2) (hc : c ≠ 0) :
    (∑ x : α × (Fin k → ZMod 2),
        (if g x.1 + (∑ j : Fin k, c j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0 := by
  classical
  have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    decide
  have h_exists : ∃ i : Fin k, c i ≠ 0 := by
    by_contra h
    apply hc
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := h_exists
  have hci : c i = 1 := by
    cases zmod2_cases (c i) with
    | inl h0 => exact False.elim (hi h0)
    | inr h1 => exact h1
  have h10 : (1 : ZMod 2) ≠ 0 := by
    decide
  have htwo : (1 : ZMod 2) + 1 = 0 := by
    decide
  let T : (Fin k → ZMod 2) → (Fin k → ZMod 2) :=
    fun y j => if j = i then y j + 1 else y j
  have hT_invol : Function.Involutive T := by
    intro y
    funext j
    by_cases hji : j = i
    · subst j
      simp [T, htwo, add_assoc]
    · simp [T, hji]
  have hT_bij : Function.Bijective T := by
    constructor
    · intro y z hyz
      calc
        y = T (T y) := (hT_invol y).symm
        _ = T (T z) := by rw [hyz]
        _ = z := hT_invol z
    · intro y
      exact ⟨T y, hT_invol y⟩
  have hlin (y : Fin k → ZMod 2) :
      (∑ j : Fin k, c j * T y j) = (∑ j : Fin k, c j * y j) + 1 := by
    calc
      (∑ j : Fin k, c j * T y j)
          = ∑ j : Fin k, (c j * y j + if j = i then c j else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · subst j
              simp [T, mul_add]
            · simp [T, hji]
      _ = (∑ j : Fin k, c j * y j) + ∑ j : Fin k, (if j = i then c j else 0) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin k, c j * y j) + c i := by
            simp
      _ = (∑ j : Fin k, c j * y j) + 1 := by
            rw [hci]
  have hinner (a : α) :
      (∑ y : Fin k → ZMod 2,
          (if g a + (∑ j : Fin k, c j * y j) = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0 := by
    let s : (Fin k → ZMod 2) → ℤ := fun y =>
      if g a + (∑ j : Fin k, c j * y j) = 0 then (1 : ℤ) else (-1 : ℤ)
    have hsumT : (∑ y : Fin k → ZMod 2, s (T y)) = ∑ y : Fin k → ZMod 2, s y := by
      let e : (Fin k → ZMod 2) ≃ (Fin k → ZMod 2) := Equiv.ofBijective T hT_bij
      change (∑ y : Fin k → ZMod 2, s (e y)) = ∑ y : Fin k → ZMod 2, s y
      simpa using (Equiv.sum_comp e s)
    have hneg : ∀ y : Fin k → ZMod 2, s (T y) = -s y := by
      intro y
      have harg :
          g a + (∑ j : Fin k, c j * T y j)
            = (g a + (∑ j : Fin k, c j * y j)) + 1 := by
        rw [hlin y]
        simp [add_assoc]
      by_cases hp : g a + (∑ j : Fin k, c j * y j) = 0
      · have hnot : ¬ g a + (∑ j : Fin k, c j * T y j) = 0 := by
          rw [harg, hp]
          simp [h10]
        simp [s, hp, hnot]
      · have hp_eq : g a + (∑ j : Fin k, c j * y j) = 1 := by
          cases zmod2_cases (g a + (∑ j : Fin k, c j * y j)) with
          | inl h0 => exact False.elim (hp h0)
          | inr h1 => exact h1
        have hpT : g a + (∑ j : Fin k, c j * T y j) = 0 := by
          rw [harg, hp_eq]
          exact htwo
        simp [s, hp, hpT]
    have hsum_neg :
        (∑ y : Fin k → ZMod 2, s (T y)) = - (∑ y : Fin k → ZMod 2, s y) := by
      calc
        (∑ y : Fin k → ZMod 2, s (T y)) = ∑ y : Fin k → ZMod 2, -s y := by
          apply Finset.sum_congr rfl
          intro y hy
          exact hneg y
        _ = - (∑ y : Fin k → ZMod 2, s y) := by
          simp
    have hEqNeg : (∑ y : Fin k → ZMod 2, s y) = - (∑ y : Fin k → ZMod 2, s y) := by
      calc
        (∑ y : Fin k → ZMod 2, s y) = (∑ y : Fin k → ZMod 2, s (T y)) := hsumT.symm
        _ = - (∑ y : Fin k → ZMod 2, s y) := hsum_neg
    have hzero : (∑ y : Fin k → ZMod 2, s y) = 0 := by
      linarith
    simpa [s] using hzero
  calc
    (∑ x : α × (Fin k → ZMod 2),
        (if g x.1 + (∑ j : Fin k, c j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ)))
        = (∑ a : α, ∑ y : Fin k → ZMod 2,
            (if g a + (∑ j : Fin k, c j * y j) = 0
             then (1 : ℤ) else (-1 : ℤ))) := by
          rw [Fintype.sum_prod_type]
    _ = 0 := by
          simp [hinner]




theorem punit_product_linear_walsh_sum_eq
    (r : ℕ) (g : ZMod 2) (c : Fin r → ZMod 2) :
    (∑ x : PUnit × (Fin r → ZMod 2),
        (if g + Finset.univ.sum (fun j : Fin r => c j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) =
    (∑ v : Fin r → ZMod 2,
        (if g + Finset.univ.sum (fun j : Fin r => c j * v j) = 0
         then (1 : ℤ) else (-1 : ℤ))) := by
  classical
  simp [Fintype.sum_prod_type]










theorem canonicalPairQuadratic_linear_walsh_sum_eq_zero
    (r : ℕ) (g : ZMod 2) (c : Fin r → ZMod 2) (hc : c ≠ 0) :
    (∑ v : Fin r → ZMod 2,
        (if g + Finset.univ.sum (fun j : Fin r => c j * v j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0 := by
  classical
  have hpair :
      (∑ x : PUnit.{1} × (Fin r → ZMod 2),
          (if g + Finset.univ.sum (fun j : Fin r => c j * x.2 j) = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0 := by
    simpa using
      (radicalLinear_nonzero_walshSum_eq_zero (α := PUnit.{1}) r (fun _ : PUnit.{1} => g) c hc)
  have hcollapse := punit_product_linear_walsh_sum_eq r g c
  exact hcollapse.symm.trans hpair




theorem canonical_pair_quadratic_reindex_uv
    (r : ℕ) (a b : Fin r → ZMod 2) (d : ZMod 2) :
    (∑ x : Fin r → ZMod 2 × ZMod 2,
        (if Finset.univ.sum (fun i : Fin r =>
              (x i).1 * (x i).2 + a i * (x i).1 + b i * (x i).2) + d = 0
         then (1 : ℤ) else (-1 : ℤ))) =
      ∑ u : Fin r → ZMod 2, ∑ v : Fin r → ZMod 2,
        (if Finset.univ.sum (fun i : Fin r =>
              u i * v i + a i * u i + b i * v i) + d = 0
         then (1 : ℤ) else (-1 : ℤ)) := by
  classical
  let pairToUV : (Fin r → ZMod 2 × ZMod 2) ≃
      ((Fin r → ZMod 2) × (Fin r → ZMod 2)) :=
    { toFun := fun x => (fun i => (x i).1, fun i => (x i).2)
      invFun := fun uv => fun i => (uv.1 i, uv.2 i)
      left_inv := by
        intro x
        ext i <;> rfl
      right_inv := by
        rintro ⟨u, v⟩
        rfl }
  calc
    (∑ x : Fin r → ZMod 2 × ZMod 2,
        (if Finset.univ.sum (fun i : Fin r =>
              (x i).1 * (x i).2 + a i * (x i).1 + b i * (x i).2) + d = 0
         then (1 : ℤ) else (-1 : ℤ)))
        = ∑ uv : (Fin r → ZMod 2) × (Fin r → ZMod 2),
            (if Finset.univ.sum (fun i : Fin r =>
                  uv.1 i * uv.2 i + a i * uv.1 i + b i * uv.2 i) + d = 0
             then (1 : ℤ) else (-1 : ℤ)) := by
          simpa [pairToUV] using
            (Equiv.sum_comp pairToUV
              (fun uv : (Fin r → ZMod 2) × (Fin r → ZMod 2) =>
                (if Finset.univ.sum (fun i : Fin r =>
                      uv.1 i * uv.2 i + a i * uv.1 i + b i * uv.2 i) + d = 0
                 then (1 : ℤ) else (-1 : ℤ))))
    _ = ∑ u : Fin r → ZMod 2, ∑ v : Fin r → ZMod 2,
        (if Finset.univ.sum (fun i : Fin r =>
              u i * v i + a i * u i + b i * v i) + d = 0
         then (1 : ℤ) else (-1 : ℤ)) := by
          rw [Fintype.sum_prod_type]




theorem outer_survivor_sum_ne_zero
    (r : ℕ) (a b : Fin r → ZMod 2) (d : ZMod 2) :
    (∑ u : Fin r → ZMod 2,
        (if u = b then
          (Fintype.card (Fin r → ZMod 2) : ℤ) *
            (if Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
             then (1 : ℤ) else (-1 : ℤ))
        else 0)) ≠ 0 := by
  classical
  let sign : ℤ :=
    if Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
    then (1 : ℤ) else (-1 : ℤ)
  have hsum :
      (∑ u : Fin r → ZMod 2,
        (if u = b then
          (Fintype.card (Fin r → ZMod 2) : ℤ) *
            (if Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
             then (1 : ℤ) else (-1 : ℤ))
        else 0))
      = (Fintype.card (Fin r → ZMod 2) : ℤ) * sign := by
    simp [sign]
  have hcard_pos_nat : 0 < Fintype.card (Fin r → ZMod 2) :=
    Fintype.card_pos_iff.mpr ⟨fun _ : Fin r => (0 : ZMod 2)⟩
  have hcard_ne : (Fintype.card (Fin r → ZMod 2) : ℤ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcard_pos_nat)
  have hsign_ne : sign ≠ 0 := by
    dsimp [sign]
    by_cases hconst : Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
    · simp [hconst]
    · simp [hconst]
  rw [hsum]
  exact mul_ne_zero hcard_ne hsign_ne












lemma canonicalPairQuadratic_zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul]
  have h2 : (2 : ZMod 2) = 0 := by
    decide
  rw [h2, zero_mul]

lemma canonicalPairQuadratic_collect_v
    (r : ℕ) (a b u v : Fin r → ZMod 2) (d : ZMod 2) :
    Finset.univ.sum (fun i : Fin r =>
        u i * v i + a i * u i + b i * v i) + d =
      (Finset.univ.sum (fun i : Fin r => a i * u i) + d) +
        Finset.univ.sum (fun i : Fin r => (u i + b i) * v i) := by
  have hsum :
      Finset.univ.sum (fun i : Fin r =>
          u i * v i + a i * u i + b i * v i) =
        Finset.univ.sum (fun i : Fin r =>
          a i * u i + (u i + b i) * v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [add_mul]
    ac_rfl
  rw [hsum, Finset.sum_add_distrib]
  ac_rfl

lemma canonicalPairQuadratic_diag_sum
    (r : ℕ) (a b v : Fin r → ZMod 2) :
    Finset.univ.sum (fun i : Fin r =>
        b i * v i + a i * b i + b i * v i) =
      Finset.univ.sum (fun i : Fin r => a i * b i) := by
  apply Finset.sum_congr rfl
  intro i hi
  calc
    b i * v i + a i * b i + b i * v i
        = (b i * v i + b i * v i) + a i * b i := by
          ac_rfl
    _ = 0 + a i * b i := by
          rw [canonicalPairQuadratic_zmod_two_add_self (b i * v i)]
    _ = a i * b i := by
          simp

lemma canonicalPairQuadratic_coeff_ne_zero_of_ne
    (r : ℕ) (u b : Fin r → ZMod 2) (h : u ≠ b) :
    (fun i : Fin r => u i + b i) ≠ 0 := by
  intro hc
  apply h
  funext i
  have hi : u i + b i = 0 := by
    have hci := congr_fun hc i
    simpa using hci
  calc
    u i = u i + 0 := by
      simp
    _ = u i + (b i + b i) := by
      rw [canonicalPairQuadratic_zmod_two_add_self (b i)]
    _ = (u i + b i) + b i := by
      ac_rfl
    _ = 0 + b i := by
      rw [hi]
    _ = b i := by
      simp

lemma canonicalPairQuadratic_inner_sum_eq
    (r : ℕ) (a b u : Fin r → ZMod 2) (d : ZMod 2) :
    (∑ v : Fin r → ZMod 2,
        (if Finset.univ.sum (fun i : Fin r =>
              u i * v i + a i * u i + b i * v i) + d = 0
         then (1 : ℤ) else (-1 : ℤ))) =
      (if u = b then
        (Fintype.card (Fin r → ZMod 2) : ℤ) *
          (if Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
           then (1 : ℤ) else (-1 : ℤ))
      else 0) := by
  classical
  by_cases h : u = b
  · subst u
    rw [if_pos rfl]
    calc
      (∑ v : Fin r → ZMod 2,
          (if Finset.univ.sum (fun i : Fin r =>
                b i * v i + a i * b i + b i * v i) + d = 0
           then (1 : ℤ) else (-1 : ℤ)))
          =
        ∑ v : Fin r → ZMod 2,
          (if Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
           then (1 : ℤ) else (-1 : ℤ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [canonicalPairQuadratic_diag_sum r a b v]
      _ =
        (Fintype.card (Fin r → ZMod 2) : ℤ) *
          (if Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
           then (1 : ℤ) else (-1 : ℤ)) := by
            simp [Finset.sum_const, Finset.card_univ]
  · rw [if_neg h]
    have hc : (fun i : Fin r => u i + b i) ≠ 0 :=
      canonicalPairQuadratic_coeff_ne_zero_of_ne r u b h
    have hlin := canonicalPairQuadratic_linear_walsh_sum_eq_zero
      r (Finset.univ.sum (fun i : Fin r => a i * u i) + d)
      (fun i : Fin r => u i + b i) hc
    calc
      (∑ v : Fin r → ZMod 2,
          (if Finset.univ.sum (fun i : Fin r =>
                u i * v i + a i * u i + b i * v i) + d = 0
           then (1 : ℤ) else (-1 : ℤ)))
          =
        ∑ v : Fin r → ZMod 2,
          (if (Finset.univ.sum (fun i : Fin r => a i * u i) + d) +
                Finset.univ.sum (fun j : Fin r => (u j + b j) * v j) = 0
           then (1 : ℤ) else (-1 : ℤ)) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [canonicalPairQuadratic_collect_v r a b u v d]
      _ = 0 := hlin

theorem canonicalPairQuadratic_signedSum_ne_zero
    (r : ℕ) (a b : Fin r → ZMod 2) (d : ZMod 2) :
    (∑ x : Fin r → ZMod 2 × ZMod 2,
        (if Finset.univ.sum (fun i : Fin r =>
              (x i).1 * (x i).2 + a i * (x i).1 + b i * (x i).2) + d = 0
         then (1 : ℤ) else (-1 : ℤ))) ≠ 0 := by
  classical
  rw [canonical_pair_quadratic_reindex_uv r a b d]
  have hcollapse :
      (∑ u : Fin r → ZMod 2, ∑ v : Fin r → ZMod 2,
          (if Finset.univ.sum (fun i : Fin r =>
                u i * v i + a i * u i + b i * v i) + d = 0
           then (1 : ℤ) else (-1 : ℤ))) =
        ∑ u : Fin r → ZMod 2,
          (if u = b then
            (Fintype.card (Fin r → ZMod 2) : ℤ) *
              (if Finset.univ.sum (fun i : Fin r => a i * b i) + d = 0
               then (1 : ℤ) else (-1 : ℤ))
          else 0) := by
    apply Finset.sum_congr rfl
    intro u hu
    exact canonicalPairQuadratic_inner_sum_eq r a b u d
  rw [hcollapse]
  exact outer_survivor_sum_ne_zero r a b d






theorem rank_block_sum_factor_of_radical_coeff_zero
    (r k : ℕ) (a b : Fin r → ZMod 2) (c : Fin k → ZMod 2) (d : ZMod 2)
    (hc : c = 0) :
    (∑ x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        (if (Finset.univ.sum (fun i : Fin r =>
              (x.1 i).1 * (x.1 i).2 + a i * (x.1 i).1 + b i * (x.1 i).2) + d)
            + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ)))
      = (Fintype.card (Fin k → ZMod 2) : ℤ) *
        (∑ y : Fin r → ZMod 2 × ZMod 2,
          (if Finset.univ.sum (fun i : Fin r =>
                (y i).1 * (y i).2 + a i * (y i).1 + b i * (y i).2) + d = 0
           then (1 : ℤ) else (-1 : ℤ))) := by
  classical
  subst c
  rw [Fintype.sum_prod_type]
  simp [Finset.mul_sum]












theorem canonicalRankBlock_signedSum_zero_iff_radicalCoeff_ne_zero
    (r k : ℕ) (a b : Fin r → ZMod 2) (c : Fin k → ZMod 2) (d : ZMod 2) :
    ((∑ x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        (if (Finset.univ.sum (fun i : Fin r =>
              (x.1 i).1 * (x.1 i).2 + a i * (x.1 i).1 + b i * (x.1 i).2) + d)
            + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0) ↔ c ≠ 0 := by
  constructor
  · intro hsum
    by_contra hnot
    have hc : c = 0 := by
      simpa using hnot
    have hfactor := rank_block_sum_factor_of_radical_coeff_zero r k a b c d hc
    have hcard_pos : 0 < Fintype.card (Fin k → ZMod 2) := Fintype.card_pos_iff.mpr inferInstance
    have hcard_ne : (Fintype.card (Fin k → ZMod 2) : ℤ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hcard_pos)
    have hblock_ne := canonicalPairQuadratic_signedSum_ne_zero r a b d
    have hprod_ne :
        (Fintype.card (Fin k → ZMod 2) : ℤ) *
          (∑ y : Fin r → ZMod 2 × ZMod 2,
            (if Finset.univ.sum (fun i : Fin r =>
                  (y i).1 * (y i).2 + a i * (y i).1 + b i * (y i).2) + d = 0
             then (1 : ℤ) else (-1 : ℤ))) ≠ 0 := by
      exact mul_ne_zero hcard_ne hblock_ne
    have hfull_ne :
        (∑ x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
          (if (Finset.univ.sum (fun i : Fin r =>
                (x.1 i).1 * (x.1 i).2 + a i * (x.1 i).1 + b i * (x.1 i).2) + d)
              + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0
           then (1 : ℤ) else (-1 : ℤ))) ≠ 0 := by
      rw [hfactor]
      exact hprod_ne
    exact hfull_ne hsum
  · intro hc
    exact radicalLinear_nonzero_walshSum_eq_zero
      (α := Fin r → ZMod 2 × ZMod 2)
      k
      (fun y : Fin r → ZMod 2 × ZMod 2 =>
        Finset.univ.sum (fun i : Fin r =>
          (y i).1 * (y i).2 + a i * (y i).1 + b i * (y i).2) + d)
      c
      hc




theorem tail_nonzero_parameter_count
    (r k : ℕ) :
    Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 //
      p.2.2.1 ≠ 0}
      = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
  classical
  let e :
      {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 //
        p.2.2.1 ≠ 0} ≃
        (Fin r → ZMod 2) × (Fin r → ZMod 2) ×
          {c : Fin k → ZMod 2 // c ≠ 0} × ZMod 2 :=
    { toFun := fun p => ⟨p.1.1, p.1.2.1, ⟨p.1.2.2.1, p.2⟩, p.1.2.2.2⟩
      invFun := fun q => ⟨⟨q.1, q.2.1, q.2.2.1.1, q.2.2.2⟩, q.2.2.1.2⟩
      left_inv := by
        rintro ⟨⟨a, b, c, d⟩, hc⟩
        rfl
      right_inv := by
        rintro ⟨a, b, ⟨c, hc⟩, d⟩
        rfl }
  have hC : Fintype.card {c : Fin k → ZMod 2 // c ≠ 0} = 2 ^ k - 1 := by
    calc
      Fintype.card {c : Fin k → ZMod 2 // c ≠ 0}
          = (Finset.univ.filter (fun c : Fin k → ZMod 2 => c ≠ 0)).card := by
              rw [Fintype.card_subtype]
      _ = (Finset.univ.erase (0 : Fin k → ZMod 2)).card := by
              congr 1
              ext c
              simp
      _ = Fintype.card (Fin k → ZMod 2) - 1 := by
              simp
      _ = 2 ^ k - 1 := by
              simp [ZMod.card]
  have hpow : 2 ^ (2 * r + 1) = 2 ^ r * 2 ^ r * 2 := by
    rw [show 2 * r + 1 = r + r + 1 by omega]
    rw [pow_add, pow_add, pow_one]
  calc
    Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 //
      p.2.2.1 ≠ 0}
        = Fintype.card ((Fin r → ZMod 2) × (Fin r → ZMod 2) ×
            {c : Fin k → ZMod 2 // c ≠ 0} × ZMod 2) := by
              exact Fintype.card_congr e
    _ = 2 ^ r * (2 ^ r * ((2 ^ k - 1) * 2)) := by
              simp [hC, ZMod.card]
    _ = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
              rw [hpow]
              ac_rfl








theorem canonicalRankBlock_balanced_affinePerturbation_count
    (r k : ℕ) :
    Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 //
      (∑ x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        (if (Finset.univ.sum (fun i : Fin r =>
              (x.1 i).1 * (x.1 i).2 + p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
            + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0}
      = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
  classical
  rw [← tail_nonzero_parameter_count r k]
  exact Fintype.card_congr
    (Equiv.subtypeEquivRight (fun p =>
      canonicalRankBlock_signedSum_zero_iff_radicalCoeff_ne_zero r k p.1 p.2.1 p.2.2.1 p.2.2.2))




theorem affine_zero_signed_sum_card_difference
    {α : Type*} [Fintype α]
    (k : ℕ) (g : α → ZMod 2) (c : Fin k → ZMod 2) :
    (∑ x : α × (Fin k → ZMod 2),
        if g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0
        then (1 : ℤ) else (-1 : ℤ))
      =
    (Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0} : ℤ)
      -
    (Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) ≠ 0} : ℤ) := by
  classical
  let p : α × (Fin k → ZMod 2) → Prop := fun x =>
    g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0
  have hsum :
      (∑ x : α × (Fin k → ZMod 2), if p x then (1 : ℤ) else (-1 : ℤ))
        = (Finset.univ.filter p).sum (fun _ => (1 : ℤ))
          + (Finset.univ.filter (fun x => ¬ p x)).sum (fun _ => (-1 : ℤ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p (fun x => if p x then (1 : ℤ) else (-1 : ℤ))]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [hx]
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [hx]
  have hpos :
      (Finset.univ.filter p).sum (fun _ => (1 : ℤ))
        = ((Finset.univ.filter p).card : ℤ) := by
    simp
  have hneg :
      (Finset.univ.filter (fun x => ¬ p x)).sum (fun _ => (-1 : ℤ))
        = -((Finset.univ.filter (fun x => ¬ p x)).card : ℤ) := by
    simp
  have hcard_pos :
      (Finset.univ.filter p).card
        = Fintype.card {x : α × (Fin k → ZMod 2) // p x} := by
    rw [Fintype.card_subtype]
  have hcard_neg :
      (Finset.univ.filter (fun x => ¬ p x)).card
        = Fintype.card {x : α × (Fin k → ZMod 2) // ¬ p x} := by
    rw [Fintype.card_subtype]
  rw [hsum, hpos, hneg, hcard_pos, hcard_neg]
  simp [p, sub_eq_add_neg]




theorem affine_fiber_card_eq_of_signed_sum_zero
    {α : Type*} [Fintype α]
    (k : ℕ) (g : α → ZMod 2) (c : Fin k → ZMod 2)
    (hsum : (∑ x : α × (Fin k → ZMod 2),
        if g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0
        then (1 : ℤ) else (-1 : ℤ)) = 0) :
    Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0}
      =
    Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) ≠ 0} := by
  classical
  have hdiff := affine_zero_signed_sum_card_difference k g c
  rw [hsum] at hdiff
  have hint :
      ((Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0} : ℤ)
      =
      (Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) ≠ 0} : ℤ)) := by
    omega
  exact_mod_cast hint






theorem radicalLinear_nonzero_balanced_fiber_card
    {α : Type*} [Fintype α]
    (k : ℕ) (g : α → ZMod 2) (c : Fin k → ZMod 2) (hc : c ≠ 0) :
    Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) = 0}
      =
    Fintype.card {x : α × (Fin k → ZMod 2) //
        g x.1 + Finset.univ.sum (fun j : Fin k => c j * x.2 j) ≠ 0} := by
  classical
  exact affine_fiber_card_eq_of_signed_sum_zero k g c (by
    simpa using radicalLinear_nonzero_walshSum_eq_zero k g c hc)




theorem standard_block_zero_diag_symmetric
    (n r : ℕ) :
    (let J : Matrix (Fin n) (Fin n) (ZMod 2) :=
        fun i j =>
          if i = j then 0
          else if (i : ℕ) < 2 * r ∧ (j : ℕ) < 2 * r ∧ (i : ℕ) / 2 = (j : ℕ) / 2 then 1
          else 0;
      (∀ i : Fin n, J i i = 0) ∧
      (∀ i j : Fin n, J i j = J j i)) := by
  classical
  dsimp
  constructor
  · intro i
    rw [if_pos rfl]
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
    · have hji : j ≠ i := fun h => hij h.symm
      have hiff :
          ((i : ℕ) < 2 * r ∧ (j : ℕ) < 2 * r ∧ (i : ℕ) / 2 = (j : ℕ) / 2) ↔
            ((j : ℕ) < 2 * r ∧ (i : ℕ) < 2 * r ∧ (j : ℕ) / 2 = (i : ℕ) / 2) := by
        constructor
        · intro h
          exact ⟨h.2.1, h.1, h.2.2.symm⟩
        · intro h
          exact ⟨h.2.1, h.1, h.2.2.symm⟩
      rw [if_neg hij, if_neg hji]
      by_cases hp :
          (i : ℕ) < 2 * r ∧ (j : ℕ) < 2 * r ∧ (i : ℕ) / 2 = (j : ℕ) / 2
      · have hq :
            (j : ℕ) < 2 * r ∧ (i : ℕ) < 2 * r ∧ (j : ℕ) / 2 = (i : ℕ) / 2 :=
          hiff.mp hp
        rw [if_pos hp, if_pos hq]
      · have hq :
            ¬ ((j : ℕ) < 2 * r ∧ (i : ℕ) < 2 * r ∧ (j : ℕ) / 2 = (i : ℕ) / 2) :=
          fun h => hp (hiff.mpr h)
        rw [if_neg hp, if_neg hq]




theorem canonical_rank_block_first_probe_zero
    (r k : ℕ)
    (x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2))
    (h : ∀ y : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        Finset.univ.sum (fun i : Fin r =>
          (x.1 i).1 * (y.1 i).2 + (x.1 i).2 * (y.1 i).1) = 0)
    (i : Fin r) :
    (x.1 i).1 = 0 := by
  classical
  let y : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2) :=
    (fun j : Fin r => ((0 : ZMod 2), if j = i then (1 : ZMod 2) else 0),
      fun _ : Fin k => 0)
  have hy :
      Finset.univ.sum (fun j : Fin r =>
        (x.1 j).1 * (if j = i then (1 : ZMod 2) else 0) +
          (x.1 j).2 * (0 : ZMod 2)) = 0 := by
    simpa [y] using h y
  have hterm : ∀ j : Fin r,
      (x.1 j).1 * (if j = i then (1 : ZMod 2) else 0) +
          (x.1 j).2 * (0 : ZMod 2) =
        if j = i then (x.1 i).1 else 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  have hsum :
      Finset.univ.sum (fun j : Fin r =>
        (x.1 j).1 * (if j = i then (1 : ZMod 2) else 0) +
          (x.1 j).2 * (0 : ZMod 2)) = (x.1 i).1 := by
    calc
      Finset.univ.sum (fun j : Fin r =>
          (x.1 j).1 * (if j = i then (1 : ZMod 2) else 0) +
            (x.1 j).2 * (0 : ZMod 2))
          = Finset.univ.sum (fun j : Fin r =>
              if j = i then (x.1 i).1 else 0) := by
            apply Finset.sum_congr
            · rfl
            · intro j hj
              exact hterm j
      _ = (x.1 i).1 := by
            simp
  exact hsum.symm.trans hy




theorem canonical_rank_block_second_probe_zero
    (r k : ℕ)
    (x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2))
    (h : ∀ y : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        Finset.univ.sum (fun i : Fin r =>
          (x.1 i).1 * (y.1 i).2 + (x.1 i).2 * (y.1 i).1) = 0)
    (i : Fin r) :
    (x.1 i).2 = 0 := by
  classical
  let y : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2) :=
    (fun j : Fin r => (if j = i then (1 : ZMod 2) else 0, (0 : ZMod 2)),
      fun _ : Fin k => 0)
  have hy :
      Finset.univ.sum (fun j : Fin r =>
        (x.1 j).1 * (0 : ZMod 2) +
          (x.1 j).2 * (if j = i then (1 : ZMod 2) else 0)) = 0 := by
    simpa [y] using h y
  have hsum :
      Finset.univ.sum (fun j : Fin r =>
        (x.1 j).1 * (0 : ZMod 2) +
          (x.1 j).2 * (if j = i then (1 : ZMod 2) else 0)) = (x.1 i).2 := by
    calc
      Finset.univ.sum (fun j : Fin r =>
          (x.1 j).1 * (0 : ZMod 2) +
            (x.1 j).2 * (if j = i then (1 : ZMod 2) else 0))
          = Finset.univ.sum (fun j : Fin r =>
              if j = i then (x.1 i).2 else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · subst j
              simp
            · simp [hji]
      _ = (x.1 i).2 := by
            simp
  rw [hsum] at hy
  exact hy










theorem canonicalRankBlock_radical_iff_pairPart_zero
    (r k : ℕ)
    (x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2)) :
    (∀ y : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        Finset.univ.sum (fun i : Fin r =>
          (x.1 i).1 * (y.1 i).2 + (x.1 i).2 * (y.1 i).1) = 0)
      ↔ x.1 = 0 := by
  classical
  constructor
  · intro h
    funext i
    apply Prod.ext
    · let y : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2) :=
        (fun j : Fin r => ((0 : ZMod 2), if j = i then (1 : ZMod 2) else 0),
          fun _ : Fin k => 0)
      have hy := h y
      simpa [y] using hy
    · let y : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2) :=
        (fun j : Fin r => (if j = i then (1 : ZMod 2) else 0, (0 : ZMod 2)),
          fun _ : Fin k => 0)
      have hy := h y
      simpa [y] using hy
  · intro hx y
    simp [hx]




theorem rank_eq_two_mul_contradicts_bound
    (n r : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ)
    (hrank_le : ∀ A : Matrix (Fin n) (Fin n) (ZMod 2), rank A ≤ n)
    (hlarge : n < 2 * r)
    (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hrank : rank A = 2 * r) : False := by
  have hlt : n < rank A := by
    rwa [hrank]
  exact (not_lt_of_ge (hrank_le A)) hlt




theorem rank_stratum_card_zero_of_rank_ne
    (n r : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ)
    (hno : ∀ A : Matrix (Fin n) (Fin n) (ZMod 2), rank A ≠ 2 * r) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      rank A = 2 * r} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun A => hno A.1 A.2.2.2⟩










theorem alternatingMatrix_rank_stratum_empty_of_rank_le
    (n r : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ)
    (hrank_le : ∀ A : Matrix (Fin n) (Fin n) (ZMod 2), rank A ≤ n)
    (hlarge : n < 2 * r) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      rank A = 2 * r} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun A =>
    have hlt : n < rank A.1 := by
      rw [A.2.2.2]
      exact hlarge
    (not_lt_of_ge (hrank_le A.1)) hlt⟩










theorem alternating_rank_stratum_product_card
    (n r : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ) :
    Fintype.card
      ({A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * r} ×
      {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) ×
          (Fin (n - 2 * r) → ZMod 2) × ZMod 2 //
        (∑ x : (Fin r → ZMod 2 × ZMod 2) ×
            (Fin (n - 2 * r) → ZMod 2),
          (if (Finset.univ.sum (fun i : Fin r =>
                (x.1 i).1 * (x.1 i).2 +
                  p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
              + Finset.univ.sum
                  (fun j : Fin (n - 2 * r) => p.2.2.1 j * x.2 j) = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0}) =
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * r} *
      Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) ×
          (Fin (n - 2 * r) → ZMod 2) × ZMod 2 //
        (∑ x : (Fin r → ZMod 2 × ZMod 2) ×
            (Fin (n - 2 * r) → ZMod 2),
          (if (Finset.univ.sum (fun i : Fin r =>
                (x.1 i).1 * (x.1 i).2 +
                  p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
              + Finset.univ.sum
                  (fun j : Fin (n - 2 * r) => p.2.2.1 j * x.2 j) = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0} := by
  let S : Type := {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * r}
  let P : Type := {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) ×
          (Fin (n - 2 * r) → ZMod 2) × ZMod 2 //
        (∑ x : (Fin r → ZMod 2 × ZMod 2) ×
            (Fin (n - 2 * r) → ZMod 2),
          (if (Finset.univ.sum (fun i : Fin r =>
                (x.1 i).1 * (x.1 i).2 +
                  p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
              + Finset.univ.sum
                  (fun j : Fin (n - 2 * r) => p.2.2.1 j * x.2 j) = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0}
  change Fintype.card (S × P) = Fintype.card S * Fintype.card P
  exact @Fintype.card_prod S P inferInstance inferInstance




theorem alternatingRankStratum_canonicalContribution_count
    (n r : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ) :
    Fintype.card
      ({A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * r} ×
      {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) ×
          (Fin (n - 2 * r) → ZMod 2) × ZMod 2 //
        (∑ x : (Fin r → ZMod 2 × ZMod 2) ×
            (Fin (n - 2 * r) → ZMod 2),
          (if (Finset.univ.sum (fun i : Fin r =>
                (x.1 i).1 * (x.1 i).2 +
                  p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
              + Finset.univ.sum
                  (fun j : Fin (n - 2 * r) => p.2.2.1 j * x.2 j) = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0})
      =
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * r} *
      (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)) := by
  rw [alternating_rank_stratum_product_card n r rank]
  rw [canonicalRankBlock_balanced_affinePerturbation_count r (n - 2 * r)]




theorem alternating_rank_strata_sigma_card
    (n : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ) :
    Fintype.card
      (Σ r : Fin (n + 1),
        ({A : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, A i i = 0) ∧
          (∀ i j : Fin n, A i j = A j i) ∧
          rank A = 2 * (r : ℕ)} ×
        {p : (Fin (r : ℕ) → ZMod 2) × (Fin (r : ℕ) → ZMod 2) ×
            (Fin (n - 2 * (r : ℕ)) → ZMod 2) × ZMod 2 //
          (∑ x : (Fin (r : ℕ) → ZMod 2 × ZMod 2) ×
              (Fin (n - 2 * (r : ℕ)) → ZMod 2),
            (if (Finset.univ.sum (fun i : Fin (r : ℕ) =>
                  (x.1 i).1 * (x.1 i).2 +
                    p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
                + Finset.univ.sum
                    (fun j : Fin (n - 2 * (r : ℕ)) => p.2.2.1 j * x.2 j) = 0
             then (1 : ℤ) else (-1 : ℤ))) = 0})) =
    ∑ r : Fin (n + 1),
      Fintype.card
        ({A : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, A i i = 0) ∧
          (∀ i j : Fin n, A i j = A j i) ∧
          rank A = 2 * (r : ℕ)} ×
        {p : (Fin (r : ℕ) → ZMod 2) × (Fin (r : ℕ) → ZMod 2) ×
            (Fin (n - 2 * (r : ℕ)) → ZMod 2) × ZMod 2 //
          (∑ x : (Fin (r : ℕ) → ZMod 2 × ZMod 2) ×
              (Fin (n - 2 * (r : ℕ)) → ZMod 2),
            (if (Finset.univ.sum (fun i : Fin (r : ℕ) =>
                  (x.1 i).1 * (x.1 i).2 +
                    p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
                + Finset.univ.sum
                    (fun j : Fin (n - 2 * (r : ℕ)) => p.2.2.1 j * x.2 j) = 0
             then (1 : ℤ) else (-1 : ℤ))) = 0}) := by
  classical
  exact Fintype.card_sigma












theorem alternatingRankStrata_canonicalContribution_sigma_count
    (n : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ) :
    Fintype.card
      (Σ r : Fin (n + 1),
        ({A : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, A i i = 0) ∧
          (∀ i j : Fin n, A i j = A j i) ∧
          rank A = 2 * (r : ℕ)} ×
        {p : (Fin (r : ℕ) → ZMod 2) × (Fin (r : ℕ) → ZMod 2) ×
            (Fin (n - 2 * (r : ℕ)) → ZMod 2) × ZMod 2 //
          (∑ x : (Fin (r : ℕ) → ZMod 2 × ZMod 2) ×
              (Fin (n - 2 * (r : ℕ)) → ZMod 2),
            (if (Finset.univ.sum (fun i : Fin (r : ℕ) =>
                  (x.1 i).1 * (x.1 i).2 +
                    p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
                + Finset.univ.sum
                    (fun j : Fin (n - 2 * (r : ℕ)) => p.2.2.1 j * x.2 j) = 0
             then (1 : ℤ) else (-1 : ℤ))) = 0})) =
    ∑ r : Fin (n + 1),
      Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * (r : ℕ)} *
        (2 ^ (2 * (r : ℕ) + 1) * (2 ^ (n - 2 * (r : ℕ)) - 1)) := by
  rw [alternating_rank_strata_sigma_card n rank]
  exact Finset.sum_congr rfl (fun r _ =>
    alternatingRankStratum_canonicalContribution_count n (r : ℕ) rank)










theorem quadraticANF_zero_eval_coefficients_zero
    (n : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (l : Fin n → ZMod 2) (c : ZMod 2)
    (hzero : ∀ x : Fin n → ZMod 2,
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          Q i j * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n => l i * x i) + c = 0)) :
    Q = 0 ∧ l = 0 ∧ c = 0 := by
  classical
  have hc : c = 0 := by
    let x0 : Fin n → ZMod 2 := fun _ => 0
    have h := hzero x0
    simpa [x0] using h
  have hl : ∀ i : Fin n, l i = 0 := by
    intro i
    let e : Fin n → ZMod 2 := fun k => if k = i then 1 else 0
    have hquad :
        (Finset.univ.sum (fun a : Fin n =>
          Finset.univ.sum (fun b : {b : Fin n // (a : ℕ) < (b : ℕ)} =>
            Q a b * e a * e b.1))) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      by_cases hai : a = i
      · have hbni : b.1 ≠ i := by
          intro hbi
          have hlt : (i : ℕ) < (i : ℕ) := by
            simpa [hai, hbi] using b.2
          exact (Nat.lt_irrefl (i : ℕ)) hlt
        simp [e, hai, hbni]
      · simp [e, hai]
    have hlin : (Finset.univ.sum (fun a : Fin n => l a * e a)) = l i := by
      calc
        (Finset.univ.sum (fun a : Fin n => l a * e a)) = l i * e i := by
          exact Finset.sum_eq_single i
            (by
              intro a _ hai
              simp [e, hai])
            (by
              intro hin
              exact False.elim (hin (Finset.mem_univ i)))
        _ = l i := by
          simp [e]
    have h := hzero e
    rw [hquad, hlin, hc] at h
    simpa using h
  have hQ : ∀ (i : Fin n) (j : {j : Fin n // (i : ℕ) < (j : ℕ)}), Q i j = 0 := by
    intro i j
    let e : Fin n → ZMod 2 := fun k => if k = i then 1 else if k = j.1 then 1 else 0
    have hlin : (Finset.univ.sum (fun a : Fin n => l a * e a)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [hl a]
      simp
    have hinner :
        (Finset.univ.sum (fun b : {b : Fin n // (i : ℕ) < (b : ℕ)} =>
          Q i b * e i * e b.1)) = Q i j := by
      calc
        (Finset.univ.sum (fun b : {b : Fin n // (i : ℕ) < (b : ℕ)} =>
          Q i b * e i * e b.1)) = Q i j * e i * e j.1 := by
            exact Finset.sum_eq_single j
              (by
                intro b _ hbne
                have hbi : b.1 ≠ i := by
                  intro hbi
                  have hlt : (i : ℕ) < (i : ℕ) := by
                    simpa [hbi] using b.2
                  exact (Nat.lt_irrefl (i : ℕ)) hlt
                have hbj : b.1 ≠ j.1 := by
                  intro hbj
                  exact hbne (Subtype.ext hbj)
                simp [e, hbi, hbj])
              (by
                intro hjnot
                exact False.elim (hjnot (Finset.mem_univ j)))
        _ = Q i j := by
            have hji : j.1 ≠ i := by
              intro hji
              have hlt : (i : ℕ) < (i : ℕ) := by
                simpa [hji] using j.2
              exact (Nat.lt_irrefl (i : ℕ)) hlt
            simp [e, hji]
    have hquad :
        (Finset.univ.sum (fun a : Fin n =>
          Finset.univ.sum (fun b : {b : Fin n // (a : ℕ) < (b : ℕ)} =>
            Q a b * e a * e b.1))) = Q i j := by
      calc
        (Finset.univ.sum (fun a : Fin n =>
          Finset.univ.sum (fun b : {b : Fin n // (a : ℕ) < (b : ℕ)} =>
            Q a b * e a * e b.1))) =
            (Finset.univ.sum (fun b : {b : Fin n // (i : ℕ) < (b : ℕ)} =>
              Q i b * e i * e b.1)) := by
              exact Finset.sum_eq_single i
                (by
                  intro a _ hai
                  apply Finset.sum_eq_zero
                  intro b _
                  by_cases haj : a = j.1
                  · have hbi : b.1 ≠ i := by
                      intro hbi
                      have hltji : (j.1 : ℕ) < (i : ℕ) := by
                        simpa [haj, hbi] using b.2
                      have hlt : (i : ℕ) < (i : ℕ) := Nat.lt_trans j.2 hltji
                      exact (Nat.lt_irrefl (i : ℕ)) hlt
                    have hbj : b.1 ≠ j.1 := by
                      intro hbj
                      have hlt : (j.1 : ℕ) < (j.1 : ℕ) := by
                        simpa [haj, hbj] using b.2
                      exact (Nat.lt_irrefl (j.1 : ℕ)) hlt
                    simp [e, haj, hbi, hbj]
                  · simp [e, hai, haj])
                (by
                  intro hin
                  exact False.elim (hin (Finset.mem_univ i)))
        _ = Q i j := hinner
    have h := hzero e
    rw [hquad, hlin, hc] at h
    simpa using h
  constructor
  · apply funext
    intro i
    apply funext
    intro j
    exact hQ i j
  constructor
  · apply funext
    intro i
    exact hl i
  · exact hc




theorem eq_of_delta_coefficients_zero
    (n : ℕ)
    (Q Q' : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (l l' : Fin n → ZMod 2) (c c' : ZMod 2)
    (hQ : (fun i : Fin n =>
      fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} => Q i j + Q' i j) = 0)
    (hl : (fun i : Fin n => l i + l' i) = 0)
    (hc : c + c' = 0) :
    Q = Q' ∧ l = l' ∧ c = c' := by
  classical
  have hscalar : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    intro a b hab
    fin_cases a
    · fin_cases b
      · rfl
      · exfalso
        have hbad : (1 : ZMod 2) = 0 := by
          change (0 : ZMod 2) + (1 : ZMod 2) = (0 : ZMod 2) at hab
          simp at hab
        exact zero_ne_one hbad.symm
    · fin_cases b
      · exfalso
        have hbad : (1 : ZMod 2) = 0 := by
          change (1 : ZMod 2) + (0 : ZMod 2) = (0 : ZMod 2) at hab
          simp at hab
        exact zero_ne_one hbad.symm
      · rfl
  constructor
  · funext i
    funext j
    apply hscalar
    simpa using congrFun (congrFun hQ i) j
  constructor
  · funext i
    apply hscalar
    simpa using congrFun hl i
  · exact hscalar c c' hc




theorem zmodTwo_add_self_eq_zero (a : ZMod 2) :
    a + a = 0 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc
    a + a = (2 : ZMod 2) * a := by ring
    _ = 0 * a := by rw [htwo]
    _ = 0 := by simp




theorem upper_triangular_quadratic_self_translate_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (x z : Fin n -> ZMod 2) :
    (let q : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1))
     let polar : (Fin n -> ZMod 2) -> (Fin n -> ZMod 2) -> ZMod 2 := fun y z =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (y i * z j.1 + z i * y j.1)))
     q (x + z) + q x = q z + polar x z) := by
  classical
  have htwo : (2 : ZMod 2) = 0 := by
    decide
  simp [Pi.add_apply, Finset.sum_add_distrib, mul_add, add_mul]
  ring_nf
  rw [htwo]
  simp




theorem upper_triangular_linear_self_translate_q2
    (n : Nat)
    (a : Fin n -> ZMod 2)
    (x z : Fin n -> ZMod 2) :
    (let lin : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n => a i * y i)
     lin (x + z) + lin x = lin z) := by
  classical
  simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  let Sx : ZMod 2 := Finset.univ.sum (fun i : Fin n => a i * x i)
  let Sz : ZMod 2 := Finset.univ.sum (fun i : Fin n => a i * z i)
  change Sx + Sz + Sx = Sz
  rw [add_assoc, add_comm Sz Sx, ← add_assoc, zmodTwo_add_self_eq_zero, zero_add]


theorem upper_triangular_phase_self_translate_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a : Fin n -> ZMod 2)
    (x z : Fin n -> ZMod 2) :
    (let q : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1))
     let lin : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n => a i * y i)
     let polar : (Fin n -> ZMod 2) -> (Fin n -> ZMod 2) -> ZMod 2 := fun y z =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (y i * z j.1 + z i * y j.1)))
     q (x + z) + lin (x + z) + (q x + lin x) =
      q z + lin z + polar x z) := by
  classical
    let q : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1))
    let lin : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n => a i * y i)
    let polar : (Fin n -> ZMod 2) -> (Fin n -> ZMod 2) -> ZMod 2 := fun y z =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (y i * z j.1 + z i * y j.1)))
    change q (x + z) + lin (x + z) + (q x + lin x) = q z + lin z + polar x z
    have hq : q (x + z) + q x = q z + polar x z := by
      simpa [q, polar] using upper_triangular_quadratic_self_translate_q2 n Q x z
    have hlin : lin (x + z) + lin x = lin z := by
      simpa [lin] using upper_triangular_linear_self_translate_q2 n a x z
    calc
      q (x + z) + lin (x + z) + (q x + lin x)
          = (q (x + z) + q x) + (lin (x + z) + lin x) := by ac_rfl
      _ = (q z + polar x z) + lin z := by rw [hq, hlin]
      _ = q z + lin z + polar x z := by ac_rfl




theorem zmod2_zero_test_sign_add (u v : ZMod 2) :
    (if u = 0 then (1 : Int) else (-1 : Int)) *
      (if v = 0 then (1 : Int) else (-1 : Int)) =
    (if u + v = 0 then (1 : Int) else (-1 : Int)) := by
  fin_cases u <;> fin_cases v <;> decide


theorem upper_triangular_phase_pair_sign_eq_self_translate_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a : Fin n -> ZMod 2)
    (x z : Fin n -> ZMod 2) :
    (let q : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1))
     let lin : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n => a i * y i)
     let polar : (Fin n -> ZMod 2) -> (Fin n -> ZMod 2) -> ZMod 2 := fun y z =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (y i * z j.1 + z i * y j.1)))
     (if q (x + z) + lin (x + z) = 0 then (1 : Int) else (-1 : Int)) *
       (if q x + lin x = 0 then (1 : Int) else (-1 : Int)) =
     (if q z + lin z + polar x z = 0 then (1 : Int) else (-1 : Int))) := by
  dsimp
  rw [← upper_triangular_phase_self_translate_q2 n Q a x z]
  exact zmod2_zero_test_sign_add _ _


theorem upper_triangular_phase_pair_sign_eq_one_of_phase_polar_zero_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a : Fin n -> ZMod 2)
    (x z : Fin n -> ZMod 2)
    (hphase :
      (let q : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * y i * y j.1))
       let lin : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
        Finset.univ.sum (fun i : Fin n => a i * y i)
       q z + lin z = 0))
    (hpolar :
      (let polar : (Fin n -> ZMod 2) -> (Fin n -> ZMod 2) -> ZMod 2 := fun y z =>
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * (y i * z j.1 + z i * y j.1)))
       polar x z = 0)) :
    (let q : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1))
     let lin : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n => a i * y i)
     (if q (x + z) + lin (x + z) = 0 then (1 : Int) else (-1 : Int)) *
       (if q x + lin x = 0 then (1 : Int) else (-1 : Int)) = (1 : Int)) := by
  simpa [hphase, hpolar] using
      (upper_triangular_phase_pair_sign_eq_self_translate_q2 n Q a x z)






theorem matrix_double_sum_split_upper_lower_diag_q2
    (n : Nat)
    (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (x y : Fin n -> ZMod 2) :
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : Fin n =>
        x i * (A i j * y j))) =
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          x i * (A i (j.1) * y (j.1))))) +
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          x (j.1) * (A (j.1) i * y i)))) +
      (Finset.univ.sum (fun i : Fin n =>
        x i * (A i i * y i))) := by
  classical
  let F : Fin n → Fin n → ZMod 2 := fun i j => x i * (A i j * y j)
  let Upper : Type := Sigma fun i : Fin n => {j : Fin n // (i : Nat) < (j : Nat)}
  let e : Sum (Sum Upper Upper) (Fin n) ≃ Fin n × Fin n :=
    { toFun := fun s =>
        match s with
        | Sum.inl (Sum.inl u) => (u.1, u.2.1)
        | Sum.inl (Sum.inr u) => (u.2.1, u.1)
        | Sum.inr i => (i, i)
      invFun := fun p =>
        if hlt : (p.1 : Nat) < (p.2 : Nat) then
          Sum.inl (Sum.inl ⟨p.1, ⟨p.2, hlt⟩⟩)
        else if hgt : (p.2 : Nat) < (p.1 : Nat) then
          Sum.inl (Sum.inr ⟨p.2, ⟨p.1, hgt⟩⟩)
        else
          Sum.inr p.1
      left_inv := by
        intro s
        cases s with
        | inl s =>
          cases s with
          | inl u =>
            rcases u with ⟨i, j, hij⟩
            simp [Upper, hij]
          | inr u =>
            rcases u with ⟨i, j, hij⟩
            have hnot : ¬ (j : Nat) < (i : Nat) := by
              exact not_lt_of_ge (Nat.le_of_lt hij)
            simp [Upper, hnot, hij]
        | inr i =>
          simp [Upper]
      right_inv := by
        intro p
        by_cases hlt : (p.1 : Nat) < (p.2 : Nat)
        · cases p with
          | mk i j =>
            simp [Upper, hlt]
        · by_cases hgt : (p.2 : Nat) < (p.1 : Nat)
          · cases p with
            | mk i j =>
              simp [Upper, hlt, hgt]
          · have hval : (p.1 : Nat) = (p.2 : Nat) := by
              exact Nat.le_antisymm (Nat.le_of_not_gt hgt) (Nat.le_of_not_gt hlt)
            cases p with
            | mk i j =>
              have hij : i = j := Fin.ext hval
              subst j
              simp [Upper] }
  have hsum :
      Finset.univ.sum (fun p : Fin n × Fin n => F p.1 p.2) =
        Finset.univ.sum (fun s : Sum (Sum Upper Upper) (Fin n) =>
          F (e s).1 (e s).2) := by
    exact
      Fintype.sum_equiv e.symm
        (fun p : Fin n × Fin n => F p.1 p.2)
        (fun s : Sum (Sum Upper Upper) (Fin n) => F (e s).1 (e s).2)
        (by
          intro a
          simp)
  simpa [F, Upper, e, Fintype.sum_prod_type, Fintype.sum_sum_type,
    Fintype.sum_sigma, add_assoc] using hsum




theorem matrix_to_lin_dot_expand_q2
    (n : Nat)
    (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (x y : Fin n -> ZMod 2) :
    Finset.univ.sum (fun i : Fin n =>
      x i * (((Matrix.toLin' A) y) i)) =
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : Fin n =>
        x i * (A i j * y j))) := by
  classical
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]


theorem upper_triangular_polar_cross_eq_matrix_dot_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (x y : Fin n -> ZMod 2) :
    (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      (fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0);
     Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (x i * y j.1 + y i * x j.1))) =
      Finset.univ.sum (fun i : Fin n =>
        x i * (((Matrix.toLin' A) y) i))) := by
  classical
      let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
        fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0
      change
        Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * (x i * y j.1 + y i * x j.1))) =
          Finset.univ.sum (fun i : Fin n =>
            x i * (((Matrix.toLin' A) y) i))
      rw [matrix_to_lin_dot_expand_q2 n A x y]
      rw [matrix_double_sum_split_upper_lower_diag_q2 n A x y]
      have hA_upper : ∀ (i : Fin n) (j : {j : Fin n // (i : Nat) < (j : Nat)}),
          A i j.1 = Q i j := by
        intro i j
        dsimp [A]
        rw [dif_pos j.2]
      have hA_lower : ∀ (i : Fin n) (j : {j : Fin n // (i : Nat) < (j : Nat)}),
          A j.1 i = Q i j := by
        intro i j
        have hnot : ¬ ((j.1 : Nat) < (i : Nat)) := Nat.not_lt.mpr (Nat.le_of_lt j.2)
        dsimp [A]
        rw [dif_neg hnot, dif_pos j.2]
      have hA_diag : ∀ i : Fin n, A i i = 0 := by
        intro i
        have hnot : ¬ ((i : Nat) < (i : Nat)) := lt_irrefl (i : Nat)
        dsimp [A]
        rw [dif_neg hnot, dif_neg hnot]
      trans
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            x i * (Q i j * y j.1) + x j.1 * (Q i j * y i)))
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      · simp only [hA_upper, hA_lower, hA_diag, zero_mul, mul_zero,
          Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]




theorem upper_triangular_polar_cross_vanishes_of_kernel_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (y : Fin n -> ZMod 2)
    (hy :
      (Matrix.toLin'
        ((fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0) : Matrix (Fin n) (Fin n) (ZMod 2))) y = 0) :
    forall x : Fin n -> ZMod 2,
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (x i * y j.1 + y i * x j.1))) = 0 := by
  classical
    intro x
    let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      (fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0)
    have hmul : Matrix.mulVec A y = 0 := hy
    calc
      Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * (x i * y j.1 + y i * x j.1)))
          = Finset.univ.sum (fun i : Fin n => x i * Matrix.mulVec A y i) := by
              simpa [A] using upper_triangular_polar_cross_eq_matrix_dot_q2 n Q x y
      _ = 0 := by
              simp [hmul]




theorem f2_function_int_sum_eq_card_of_pointwise_one_q2
    (n : Nat) (f : (Fin n → ZMod 2) → ℤ)
    (hf : ∀ x : Fin n → ZMod 2, f x = (1 : ℤ)) :
    Finset.univ.sum f = (Fintype.card (Fin n → ZMod 2) : ℤ) := by
  classical
  calc
    Finset.univ.sum f =
        Finset.univ.sum (fun _ : Fin n → ZMod 2 => (1 : ℤ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hf x
    _ = (Fintype.card (Fin n → ZMod 2) : ℤ) := by
      simp


theorem upper_triangular_kernel_phase_pair_sign_sum_eq_card_q2
    (n : Nat)
    (Q : (i : Fin n) → {j : Fin n // (i : Nat) < (j : Nat)} → ZMod 2)
    (a : Fin n → ZMod 2)
    (z : Fin n → ZMod 2)
    (hz :
      (Matrix.toLin'
        ((fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0) : Matrix (Fin n) (Fin n) (ZMod 2))) z = 0)
    (hphase :
      Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * z i * z j.1)) +
        Finset.univ.sum (fun i : Fin n => a i * z i) = 0) :
    Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
      (if
        Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * (x + z) i * (x + z) j.1)) +
          Finset.univ.sum (fun i : Fin n => a i * (x + z) i) = 0 then
        (1 : ℤ)
      else
        (-1 : ℤ)) *
      (if
        Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => a i * x i) = 0 then
        (1 : ℤ)
      else
        (-1 : ℤ))) =
      (Fintype.card (Fin n → ZMod 2) : ℤ) := by
  classical
  apply f2_function_int_sum_eq_card_of_pointwise_one_q2 n
  intro x
  exact upper_triangular_phase_pair_sign_eq_one_of_phase_polar_zero_q2 n Q a x z (by
    simpa using hphase) (by
    simpa using (upper_triangular_polar_cross_vanishes_of_kernel_q2 n Q z hz x))
















theorem matrix_affine_linear_sign_sum_eq_zero_q2
    (n : Nat)
    (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (z : Fin n → ZMod 2)
    (b : ZMod 2)
    (hz : (Matrix.toLin' A) z ≠ 0) :
    (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      (if b + Finset.univ.sum (fun i : Fin n =>
            ((Matrix.toLin' A) z) i * x i) = 0 then
        (1 : ℤ)
      else
        (-1 : ℤ)))) = 0 := by
  classical
    let c : Fin n → ZMod 2 := (Matrix.toLin' A) z
    have hc : c ≠ 0 := by
      simpa [c] using hz
    have hprod :
        (Finset.univ.sum (fun x : PUnit.{1} × (Fin n → ZMod 2) =>
          (if b + Finset.univ.sum (fun j : Fin n => c j * x.2 j) = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)))) = 0 := by
      simpa using
        (radicalLinear_nonzero_walshSum_eq_zero (α := PUnit.{1}) n
          (fun _ : PUnit.{1} => b) c hc)
    have hcollapse :
        (Finset.univ.sum (fun x : PUnit.{1} × (Fin n → ZMod 2) =>
          (if b + Finset.univ.sum (fun j : Fin n => c j * x.2 j) = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)))) =
        (Finset.univ.sum (fun v : Fin n → ZMod 2 =>
          (if b + Finset.univ.sum (fun j : Fin n => c j * v j) = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)))) := by
      simpa using (punit_product_linear_walsh_sum_eq n b c)
    have hvec :
        (Finset.univ.sum (fun v : Fin n → ZMod 2 =>
          (if b + Finset.univ.sum (fun j : Fin n => c j * v j) = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)))) = 0 := by
      exact Eq.trans hcollapse.symm hprod
    simpa [c] using hvec


theorem upper_triangular_nonkernel_phase_pair_sign_sum_eq_zero_q2
    (n : Nat)
    (Q : (i : Fin n) → {j : Fin n // (i : Nat) < (j : Nat)} → ZMod 2)
    (a : Fin n → ZMod 2)
    (z : Fin n → ZMod 2)
    (hz :
      (Matrix.toLin'
        ((fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0) : Matrix (Fin n) (Fin n) (ZMod 2))) z ≠ 0) :
    Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
      (if
        Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * (x + z) i * (x + z) j.1)) +
          Finset.univ.sum (fun i : Fin n => a i * (x + z) i) = 0 then
        (1 : ℤ)
      else
        (-1 : ℤ)) *
      (if
        Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => a i * x i) = 0 then
        (1 : ℤ)
      else
        (-1 : ℤ))) = 0 := by
  classical
    let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      (fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0)
    let q : (Fin n → ZMod 2) → ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1))
    let lin : (Fin n → ZMod 2) → ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n => a i * y i)
    let polar : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2 := fun y w =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (y i * w j.1 + w i * y j.1)))
    let b : ZMod 2 := q z + lin z
    have hzA : (Matrix.toLin' A) z ≠ 0 := by
      simpa [A] using hz
    have hsum :
        Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
          (if q (x + z) + lin (x + z) = 0 then (1 : ℤ) else (-1 : ℤ)) *
          (if q x + lin x = 0 then (1 : ℤ) else (-1 : ℤ))) =
        Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
          (if b + Finset.univ.sum (fun i : Fin n => ((Matrix.toLin' A) z) i * x i) = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      trans (if q z + lin z + polar x z = 0 then (1 : ℤ) else (-1 : ℤ))
      · simpa [q, lin, polar] using
          (upper_triangular_phase_pair_sign_eq_self_translate_q2 n Q a x z)
      · have hpolar : polar x z = Finset.univ.sum (fun i : Fin n => x i * ((Matrix.toLin' A) z) i) := by
          simpa [A, polar] using (upper_triangular_polar_cross_eq_matrix_dot_q2 n Q x z)
        have hdot :
            Finset.univ.sum (fun i : Fin n => x i * ((Matrix.toLin' A) z) i) =
            Finset.univ.sum (fun i : Fin n => ((Matrix.toLin' A) z) i * x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        simpa [b, add_assoc] using congrArg (fun t : ZMod 2 => if q z + lin z + t = 0 then (1 : ℤ) else (-1 : ℤ)) (hpolar.trans hdot)
    rw [hsum]
    exact matrix_affine_linear_sign_sum_eq_zero_q2 n A z b hzA




theorem upper_triangular_kernel_coset_second_moment_pos_q2
    (n : Nat)
    (Q : (i : Fin n) → {j : Fin n // (i : Nat) < (j : Nat)} → ZMod 2)
    (a : Fin n → ZMod 2)
    (hker : ∀ y : Fin n → ZMod 2,
      (Matrix.toLin' ((fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then Q j (Subtype.mk i h')
        else 0) : Matrix (Fin n) (Fin n) (ZMod 2))) y = 0 →
      Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * y i * y j.1)) +
        Finset.univ.sum (fun i : Fin n => a i * y i) = 0) :
    0 < (let phase : (Fin n → ZMod 2) → ZMod 2 := fun x =>
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n => a i * x i);
      Finset.univ.sum (fun z : Fin n → ZMod 2 =>
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          (if phase (x + z) = 0 then (1 : ℤ) else (-1 : ℤ)) *
          (if phase x = 0 then (1 : ℤ) else (-1 : ℤ))))) := by
  classical
  dsimp only
  apply Finset.sum_pos'
  · intro z _hzmem
    by_cases hzker :
        (Matrix.toLin' ((fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then Q j (Subtype.mk i h')
          else 0) : Matrix (Fin n) (Fin n) (ZMod 2))) z = 0
    · have hphasez := hker z hzker
      have hsum :=
        upper_triangular_kernel_phase_pair_sign_sum_eq_card_q2 n Q a z hzker hphasez
      rw [hsum]
      exact Int.natCast_nonneg (Fintype.card (Fin n → ZMod 2))
    · have hsum :=
        upper_triangular_nonkernel_phase_pair_sign_sum_eq_zero_q2 n Q a z hzker
      rw [hsum]
  · exact
      ⟨(0 : Fin n → ZMod 2), Finset.mem_univ (0 : Fin n → ZMod 2), by
        have hzker :
            (Matrix.toLin' ((fun i j : Fin n =>
              if h : (i : Nat) < (j : Nat) then Q i (Subtype.mk j h)
              else if h' : (j : Nat) < (i : Nat) then Q j (Subtype.mk i h')
              else 0) : Matrix (Fin n) (Fin n) (ZMod 2))) (0 : Fin n → ZMod 2) = 0 := by
          simp
        have hphase0 := hker (0 : Fin n → ZMod 2) hzker
        have hsum :=
          upper_triangular_kernel_phase_pair_sign_sum_eq_card_q2 n Q a
            (0 : Fin n → ZMod 2) hzker hphase0
        rw [hsum]
        have hcard : 0 < Fintype.card (Fin n → ZMod 2) := by
          exact Fintype.card_pos
        exact Int.natCast_pos.mpr hcard⟩




theorem f2_function_sum_square_reindex_add
    (n : Nat) (w : (Fin n → ZMod 2) → ℤ) :
    (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x)) *
        (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x)) =
      Finset.univ.sum (fun z : Fin n → ZMod 2 =>
        Finset.univ.sum (fun x : Fin n → ZMod 2 => w (x + z) * w x)) := by
  classical
  calc
    (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x)) *
        (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x))
        = Finset.univ.sum (fun x : Fin n → ZMod 2 =>
            Finset.univ.sum (fun y : Fin n → ZMod 2 => w y * w x)) := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_comm
    _ = Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          Finset.univ.sum (fun z : Fin n → ZMod 2 => w (x + z) * w x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact
            (Fintype.sum_equiv (Equiv.addLeft x)
              (fun z : Fin n → ZMod 2 => w (x + z) * w x)
              (fun y : Fin n → ZMod 2 => w y * w x)
              (fun z => rfl)).symm
    _ = Finset.univ.sum (fun z : Fin n → ZMod 2 =>
          Finset.univ.sum (fun x : Fin n → ZMod 2 => w (x + z) * w x)) := by
          exact Finset.sum_comm


theorem upperTriangular_walsh_nonzero_of_vanishes_on_kernel_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a : Fin n -> ZMod 2) :
    (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      (fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0);
     let phase : (Fin n -> ZMod 2) -> ZMod 2 := fun x =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * x i * x j.1)) +
      Finset.univ.sum (fun i : Fin n => a i * x i);
     (forall y : (Fin n -> ZMod 2),
        (Matrix.toLin' A) y = 0 -> phase y = 0) ->
       (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
          if phase x = 0 then
            (1 : Int)
          else
            (-1 : Int))) != 0) := by
  classical
    dsimp
    intro hker
    let phase : (Fin n → ZMod 2) → ZMod 2 := fun x =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * x i * x j.1)) +
      Finset.univ.sum (fun i : Fin n => a i * x i)
    let w : (Fin n → ZMod 2) → ℤ := fun x => if phase x = 0 then (1 : ℤ) else (-1 : ℤ)
    have hsecond :
        0 < Finset.univ.sum (fun z : Fin n → ZMod 2 =>
          Finset.univ.sum (fun x : Fin n → ZMod 2 => w (x + z) * w x)) := by
      simpa [phase, w] using
        (upper_triangular_kernel_coset_second_moment_pos_q2 (n := n) (Q := Q) (a := a) (hker := hker))
    have hsq :
        (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x)) *
          (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x)) =
          Finset.univ.sum (fun z : Fin n → ZMod 2 =>
            Finset.univ.sum (fun x : Fin n → ZMod 2 => w (x + z) * w x)) := by
      simpa using (f2_function_sum_square_reindex_add (n := n) w)
    have hsq_nonzero :
        (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x)) *
          (Finset.univ.sum (fun x : Fin n → ZMod 2 => w x)) ≠ 0 := by
      exact ne_of_gt (by simpa [hsq] using hsecond)
    have hnonzero : Finset.univ.sum (fun x : Fin n → ZMod 2 => w x) ≠ 0 := by
      intro hs
      exact hsq_nonzero (by simp [hs])
    simpa [phase, w] using hnonzero






theorem upper_triangular_quadratic_add_expand_with_polar_q2
    (n : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (x y : Fin n → ZMod 2) :
    (let q : (Fin n → ZMod 2) → ZMod 2 := fun z =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          Q i j * z i * z j.1));
     q (x + y) =
      q x + q y +
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            Q i j * (x i * y j.1 + y i * x j.1)))) := by
  classical
  simp only [Pi.add_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  ring_nf






theorem upper_triangular_phase_translate_of_kernel_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a : Fin n -> ZMod 2)
    (y : Fin n -> ZMod 2)
    (hy :
      (Matrix.toLin'
        ((fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0) : Matrix (Fin n) (Fin n) (ZMod 2))) y = 0) :
    forall x : Fin n -> ZMod 2,
      (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * (x + y) i * (x + y) j.1)) +
        Finset.univ.sum (fun i : Fin n => a i * (x + y) i)) =
      (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n => a i * x i)) +
      (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * y i * y j.1)) +
        Finset.univ.sum (fun i : Fin n => a i * y i)) := by
  classical
  intro x
  let q : (Fin n -> ZMod 2) -> ZMod 2 := fun z =>
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
        Q i j * z i * z j.1))
  let lin : (Fin n -> ZMod 2) -> ZMod 2 := fun z =>
    Finset.univ.sum (fun i : Fin n => a i * z i)
  let polar : ZMod 2 :=
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
        Q i j * (x i * y j.1 + y i * x j.1)))
  have hq : q (x + y) = q x + q y + polar := by
    simpa [q, polar] using upper_triangular_quadratic_add_expand_with_polar_q2 n Q x y
  have hp : polar = 0 := by
    simpa [polar] using upper_triangular_polar_cross_vanishes_of_kernel_q2 n Q y hy x
  have hlin : lin (x + y) = lin x + lin y := by
    simp [lin, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  change q (x + y) + lin (x + y) = (q x + lin x) + (q y + lin y)
  rw [hq, hp, hlin]
  ring




theorem signed_sum_nonzero_of_translate_add_q2
    (n : ℕ)
    (phi : (Fin n → ZMod 2) → ZMod 2)
    (y : Fin n → ZMod 2)
    (htranslate : ∀ x : Fin n → ZMod 2, phi (x + y) = phi x + phi y)
    (hW :
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if phi x = 0 then
          (1 : ℤ)
        else
          (-1 : ℤ))) ≠ 0) :
    phi y = 0 := by
  classical
    by_contra hphi
    have hy_one : phi y = 1 := by
      have h : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by
        decide
      exact h (phi y) hphi
    let sign : (Fin n → ZMod 2) → ℤ := fun x => if phi x = 0 then (1 : ℤ) else (-1 : ℤ)
    let e : (Fin n → ZMod 2) ≃ (Fin n → ZMod 2) :=
      { toFun := fun x => x + y
        invFun := fun x => x + y
        left_inv := by
          intro x
          funext i
          simp [Pi.add_apply, add_assoc, zmodTwo_add_self_eq_zero]
        right_inv := by
          intro x
          funext i
          simp [Pi.add_apply, add_assoc, zmodTwo_add_self_eq_zero] }
    have hperm : (Finset.univ.sum sign) = Finset.univ.sum (fun x => sign (e x)) := by
      symm
      simpa using (Fintype.sum_equiv e (fun x => sign (e x)) sign (by intro x; rfl))
    have hflip : ∀ x : Fin n → ZMod 2, sign (x + y) = - sign x := by
      intro x
      have hcase : ∀ a : ZMod 2,
          (if a + 1 = 0 then (1 : ℤ) else (-1 : ℤ)) =
            - (if a = 0 then (1 : ℤ) else (-1 : ℤ)) := by
        decide
      rw [show sign (x + y) = (if phi (x + y) = 0 then (1 : ℤ) else (-1 : ℤ)) by rfl]
      rw [htranslate x, hy_one]
      simpa [sign] using hcase (phi x)
    have hsum_neg : Finset.univ.sum (fun x => sign (e x)) = - Finset.univ.sum sign := by
      rw [Finset.sum_congr rfl (by intro x hx; exact hflip x)]
      simp [Finset.sum_neg_distrib]
    have hsum_eq_neg : Finset.univ.sum sign = - Finset.univ.sum sign := by
      calc
        Finset.univ.sum sign = Finset.univ.sum (fun x => sign (e x)) := hperm
        _ = - Finset.univ.sum sign := hsum_neg
    have hzero : Finset.univ.sum sign = 0 := by
      omega
    exact hW (by simpa [sign] using hzero)


theorem upperTriangular_walsh_nonzero_vanishes_on_kernel_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a : Fin n -> ZMod 2)
    (hW :
      (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
          if (Finset.univ.sum (fun i : Fin n =>
                Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                  Q i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => a i * x i) = 0) then
            (1 : Int)
          else
            (-1 : Int))) ≠ 0) :
    forall y : (Fin n -> ZMod 2),
      ((Matrix.toLin'
        ((fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0) : Matrix (Fin n) (Fin n) (ZMod 2))) y) = 0 ->
        Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * y i * y j.1)) +
          Finset.univ.sum (fun i : Fin n => a i * y i) = 0 := by
  exact fun y hy => by
      let phi : (Fin n -> ZMod 2) -> ZMod 2 := fun z =>
        Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * z i * z j.1)) +
          Finset.univ.sum (fun i : Fin n => a i * z i)
      have htranslate : ∀ x : Fin n -> ZMod 2, phi (x + y) = phi x + phi y := by
        intro x
        simpa [phi] using (upper_triangular_phase_translate_of_kernel_q2 n Q a y hy x)
      have hWphi :
          (Finset.univ.sum (fun x : Fin n -> ZMod 2 =>
            if phi x = 0 then
              (1 : Int)
            else
              (-1 : Int))) ≠ 0 := by
        simpa [phi] using hW
      have hyphi : phi y = 0 :=
        signed_sum_nonzero_of_translate_add_q2 n phi y htranslate hWphi
      simpa [phi] using hyphi


theorem upperTriangular_walsh_nonzero_iff_vanishes_on_kernel_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a : Fin n -> ZMod 2) :
    (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      (fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0);
     let phase : (Fin n -> ZMod 2) -> ZMod 2 := fun x =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * x i * x j.1)) +
      Finset.univ.sum (fun i : Fin n => a i * x i);
     (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if phase x = 0 then (1 : Int) else (-1 : Int)) ≠ 0) ↔
      (forall y : (Fin n -> ZMod 2),
        (Matrix.toLin' A) y = 0 -> phase y = 0)) := by
  exact Iff.intro
      (fun hW => by
        dsimp at hW ⊢
        exact upperTriangular_walsh_nonzero_vanishes_on_kernel_q2 n Q a hW)
      (fun hker => by
        dsimp at hker ⊢
        simpa using upperTriangular_walsh_nonzero_of_vanishes_on_kernel_q2 n Q a hker)




theorem upper_triangular_quadratic_coeff_to_alt_matrix_valid_q2
    (n : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) :
    (∀ i : Fin n,
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0) i i = 0) ∧
    (∀ i j : Fin n,
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0) i j =
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0) j i) := by
  exact And.intro
    (fun i => by
      simp)
    (fun i j => by
      by_cases hij : (i : ℕ) < (j : ℕ)
      case pos =>
        have hji : ¬ (j : ℕ) < (i : ℕ) := not_lt.mpr (Nat.le_of_lt hij)
        simp [hij, hji]
      case neg =>
        by_cases hji : (j : ℕ) < (i : ℕ)
        case pos =>
          simp [hij, hji]
        case neg =>
          simp [hij, hji])












theorem rank_stratum_rhs_zero_of_lt_two_mul (n r : ℕ) (h : n < 2 * r) :
    (2 ^ (r * (r - 1)) *
        (∏ i : Fin (2 * r), (2 ^ (n - (i : ℕ)) - 1))) /
      (∏ i : Fin r, (2 ^ (2 * ((i : ℕ) + 1)) - 1)) = 0 := by
  classical
    have hprod :
        (∏ i : Fin (2 * r), (2 ^ (n - (i : ℕ)) - 1)) = 0 := by
      rw [Finset.prod_eq_zero_iff]
      exact ⟨⟨n, h⟩, by simp, by simp⟩
    simp [hprod]




theorem matrix_tolin_range_finrank_le
    (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) ≤ n := by
  simpa using
    (Submodule.finrank_le (LinearMap.range (A.toLin')) :
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) ≤
        Module.finrank (ZMod 2) (Fin n → ZMod 2))




theorem alternating_matrix_tolin_rank_stratum_card_zero_of_lt_two_mul
    (n r : ℕ) (h : n < 2 * r) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r} = 0 := by
  exact alternatingMatrix_rank_stratum_empty_of_rank_le n r
    (fun A : Matrix (Fin n) (Fin n) (ZMod 2) =>
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')))
    (fun A => matrix_tolin_range_finrank_le n A) h






theorem alternatingMatrix_toLinRank_stratum_card_closed_of_lt_two_mul
    (n r : ℕ) (h : n < 2 * r) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r}
      =
      (2 ^ (r * (r - 1)) *
        (∏ i : Fin (2 * r), (2 ^ (n - (i : ℕ)) - 1))) /
        (∏ i : Fin r, (2 ^ (2 * ((i : ℕ) + 1)) - 1)) := by
  rw [alternating_matrix_tolin_rank_stratum_card_zero_of_lt_two_mul n r h,
    rank_stratum_rhs_zero_of_lt_two_mul n r h]










theorem nonzero_coefficient_pair_count
    (n : ℕ) :
    Fintype.card {p : (Fin n → ZMod 2) × ZMod 2 // p.1 ≠ 0}
      = 2 * (2 ^ n - 1) := by
  classical
  let e : {p : (Fin n → ZMod 2) × ZMod 2 // p.1 ≠ 0} ≃
      ({c : Fin n → ZMod 2 // c ≠ 0} × ZMod 2) := {
    toFun := fun p => (⟨p.1.1, p.2⟩, p.1.2)
    invFun := fun q => ⟨(q.1.1, q.2), q.1.2⟩
    left_inv := by
      intro p
      cases p with
      | mk val property =>
        cases val with
        | mk coeff const =>
          rfl
    right_inv := by
      intro q
      cases q with
      | mk coeff const =>
        cases coeff with
        | mk coeffValue coeffProperty =>
          rfl }
  have hnonzero : Fintype.card {c : Fin n → ZMod 2 // c ≠ 0} = 2 ^ n - 1 := by
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter fun c : Fin n → ZMod 2 => c ≠ 0) =
        Finset.univ.erase (0 : Fin n → ZMod 2) := by
      ext c
      simp
    rw [hfilter, Finset.card_erase_of_mem]
    · simp
    · simp
  calc
    Fintype.card {p : (Fin n → ZMod 2) × ZMod 2 // p.1 ≠ 0}
        = Fintype.card ({c : Fin n → ZMod 2 // c ≠ 0} × ZMod 2) := Fintype.card_congr e
    _ = 2 * (2 ^ n - 1) := by
      simp [hnonzero, Nat.mul_comm]












private theorem balancedAffine_zeroCoeff_signedSum_ne_zero
    (n : ℕ) (b : ZMod 2) :
    (∑ x : Fin n → ZMod 2,
        (if Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) + b = 0
         then (1 : ℤ) else (-1 : ℤ))) ≠ 0 := by
  classical
  have hposNat : 0 < Fintype.card (Fin n → ZMod 2) :=
    Fintype.card_pos_iff.mpr ⟨(0 : Fin n → ZMod 2)⟩
  have hposInt : (0 : ℤ) < (Fintype.card (Fin n → ZMod 2) : ℤ) := by
    exact_mod_cast hposNat
  by_cases hb : b = 0
  · have hsum :
        (∑ x : Fin n → ZMod 2,
            (if Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) + b = 0
             then (1 : ℤ) else (-1 : ℤ)))
          = (Fintype.card (Fin n → ZMod 2) : ℤ) := by
      calc
        (∑ x : Fin n → ZMod 2,
            (if Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) + b = 0
             then (1 : ℤ) else (-1 : ℤ)))
            = (∑ x : Fin n → ZMod 2, (1 : ℤ)) := by
                apply Finset.sum_congr rfl
                intro x hx
                have hzero :
                    Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) = 0 := by
                  apply Finset.sum_eq_zero
                  intro i hi
                  simp
                have hcond :
                    Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) + b = 0 := by
                  rw [hzero, hb]
                  simp
                rw [if_pos hcond]
        _ = (Fintype.card (Fin n → ZMod 2) : ℤ) := by
                simp
    rw [hsum]
    exact ne_of_gt hposInt
  · have hsum :
        (∑ x : Fin n → ZMod 2,
            (if Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) + b = 0
             then (1 : ℤ) else (-1 : ℤ)))
          = - (Fintype.card (Fin n → ZMod 2) : ℤ) := by
      calc
        (∑ x : Fin n → ZMod 2,
            (if Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) + b = 0
             then (1 : ℤ) else (-1 : ℤ)))
            = (∑ x : Fin n → ZMod 2, (-1 : ℤ)) := by
                apply Finset.sum_congr rfl
                intro x hx
                have hzero :
                    Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) = 0 := by
                  apply Finset.sum_eq_zero
                  intro i hi
                  simp
                have hcond :
                    Finset.univ.sum (fun i : Fin n => (0 : Fin n → ZMod 2) i * x i) + b ≠ 0 := by
                  rw [hzero]
                  simpa using hb
                rw [if_neg hcond]
        _ = - (Fintype.card (Fin n → ZMod 2) : ℤ) := by
                simp
    rw [hsum]
    have hneg : - (Fintype.card (Fin n → ZMod 2) : ℤ) < 0 := by
      linarith
    exact ne_of_lt hneg

private theorem balancedAffine_nonzeroCoeff_signedSum_eq_zero
    (n : ℕ) (p : (Fin n → ZMod 2) × ZMod 2) (hp : p.1 ≠ 0) :
    (∑ x : Fin n → ZMod 2,
        (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0 := by
  classical
  calc
    (∑ x : Fin n → ZMod 2,
        (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
         then (1 : ℤ) else (-1 : ℤ)))
        =
      (∑ x : Fin n → ZMod 2,
        (if p.2 + Finset.univ.sum (fun i : Fin n => p.1 i * x i) = 0
         then (1 : ℤ) else (-1 : ℤ))) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hcomm :
              Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 =
                p.2 + Finset.univ.sum (fun i : Fin n => p.1 i * x i) := by
            exact add_comm _ _
          rw [hcomm]
    _ = 0 := by
          exact canonicalPairQuadratic_linear_walsh_sum_eq_zero n p.2 p.1 hp

theorem balancedAffine_signedSum_count
    (n : ℕ) :
    Fintype.card {p : (Fin n → ZMod 2) × ZMod 2 //
      (∑ x : Fin n → ZMod 2,
        (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0}
      = 2 * (2 ^ n - 1) := by
  classical
  have hpred :
      ∀ p : (Fin n → ZMod 2) × ZMod 2,
        ((∑ x : Fin n → ZMod 2,
          (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0) ↔ p.1 ≠ 0 := by
    intro p
    constructor
    · intro hsum hp0
      rcases p with ⟨c, b⟩
      dsimp at hp0 hsum ⊢
      subst c
      exact (balancedAffine_zeroCoeff_signedSum_ne_zero n b) hsum
    · intro hp
      exact balancedAffine_nonzeroCoeff_signedSum_eq_zero n p hp
  let e :
      {p : (Fin n → ZMod 2) × ZMod 2 //
        (∑ x : Fin n → ZMod 2,
          (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0} ≃
      {p : (Fin n → ZMod 2) × ZMod 2 // p.1 ≠ 0} :=
    { toFun := fun p => ⟨p.1, (hpred p.1).mp p.2⟩
      invFun := fun p => ⟨p.1, (hpred p.1).mpr p.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        rfl
      right_inv := by
        intro p
        apply Subtype.ext
        rfl }
  calc
    Fintype.card {p : (Fin n → ZMod 2) × ZMod 2 //
      (∑ x : Fin n → ZMod 2,
        (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0}
        = Fintype.card {p : (Fin n → ZMod 2) × ZMod 2 // p.1 ≠ 0} := by
            exact Fintype.card_congr e
    _ = 2 * (2 ^ n - 1) := by
            exact nonzero_coefficient_pair_count n










theorem equiv_signed_sum_transport
    (r k : ℕ) (α : Type*) [Fintype α]
    (e : α ≃ (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2))
    (p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2) :
    (∑ x : α,
        (if (Finset.univ.sum (fun i : Fin r =>
              ((e x).1 i).1 * ((e x).1 i).2 +
                p.1 i * ((e x).1 i).1 + p.2.1 i * ((e x).1 i).2) + p.2.2.2)
            + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * (e x).2 j) = 0
         then (1 : ℤ) else (-1 : ℤ)))
      =
      (∑ x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        (if (Finset.univ.sum (fun i : Fin r =>
              (x.1 i).1 * (x.1 i).2 +
                p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
            + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) := by
  classical
  let β := (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2)
  let f : β → ℤ := fun x =>
    if (Finset.univ.sum (fun i : Fin r =>
          (x.1 i).1 * (x.1 i).2 +
            p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
        + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * x.2 j) = 0
    then (1 : ℤ) else (-1 : ℤ)
  change (∑ x : α, f (e x)) = ∑ x : β, f x
  exact e.sum_comp f




theorem canonicalRankBlock_balanced_affinePerturbation_count_after_equiv
    (r k : ℕ) (α : Type*) [Fintype α]
    (e : α ≃ (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2)) :
    Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 //
      (∑ x : α,
        (if (Finset.univ.sum (fun i : Fin r =>
              ((e x).1 i).1 * ((e x).1 i).2 +
                p.1 i * ((e x).1 i).1 + p.2.1 i * ((e x).1 i).2) + p.2.2.2)
            + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * (e x).2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0}
      = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
  calc
    Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 //
      (∑ x : α,
        (if (Finset.univ.sum (fun i : Fin r =>
              ((e x).1 i).1 * ((e x).1 i).2 +
                p.1 i * ((e x).1 i).1 + p.2.1 i * ((e x).1 i).2) + p.2.2.2)
            + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * (e x).2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0}
        = Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 //
      (∑ x : (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2),
        (if (Finset.univ.sum (fun i : Fin r =>
              (x.1 i).1 * (x.1 i).2 + p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
            + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * x.2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0} := by
      exact Fintype.card_congr
        { toFun := fun p =>
            ⟨p.1, by
              simpa [← equiv_signed_sum_transport r k α e p.1] using p.2⟩
          invFun := fun p =>
            ⟨p.1, by
              simpa [equiv_signed_sum_transport r k α e p.1] using p.2⟩
          left_inv := by
            intro p
            cases p
            rfl
          right_inv := by
            intro p
            cases p
            rfl }
    _ = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
      exact canonicalRankBlock_balanced_affinePerturbation_count r k












theorem balancedParam_count_of_canonicalTransport
    (r k : ℕ) (α β : Type*) [Fintype α] [Fintype β]
    (e : α ≃ (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2))
    (paramEquiv : β ≃ (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2)
    (P : β → Prop) [DecidablePred P]
    (hP : ∀ b : β,
      P b ↔
      (∑ x : α,
        (if (Finset.univ.sum (fun i : Fin r =>
              ((e x).1 i).1 * ((e x).1 i).2 +
                (paramEquiv b).1 i * ((e x).1 i).1 + (paramEquiv b).2.1 i * ((e x).1 i).2) + (paramEquiv b).2.2.2)
            + Finset.univ.sum (fun j : Fin k => (paramEquiv b).2.2.1 j * (e x).2 j) = 0
         then (1 : ℤ) else (-1 : ℤ))) = 0) :
    Fintype.card {b : β // P b} = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
  let Q : ((Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2) → Prop := fun p =>
    (∑ x : α,
      (if (Finset.univ.sum (fun i : Fin r =>
            ((e x).1 i).1 * ((e x).1 i).2 +
              p.1 i * ((e x).1 i).1 + p.2.1 i * ((e x).1 i).2) + p.2.2.2)
          + Finset.univ.sum (fun j : Fin k => p.2.2.1 j * (e x).2 j) = 0
       then (1 : ℤ) else (-1 : ℤ))) = 0
  let transportEquiv : {b : β // P b} ≃
      {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 // Q p} :=
    { toFun := fun b => ⟨paramEquiv b.1, by
        show Q (paramEquiv b.1)
        exact (hP b.1).mp b.2⟩
      invFun := fun p => ⟨paramEquiv.symm p.1, by
        apply (hP (paramEquiv.symm p.1)).mpr
        show Q (paramEquiv (paramEquiv.symm p.1))
        simpa using p.2⟩
      left_inv := by
        intro b
        apply Subtype.ext
        exact paramEquiv.symm_apply_apply b.1
      right_inv := by
        intro p
        apply Subtype.ext
        exact paramEquiv.apply_symm_apply p.1 }
  calc
    Fintype.card {b : β // P b}
        = Fintype.card {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2 // Q p} :=
          Fintype.card_congr transportEquiv
    _ = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
      simpa [Q] using canonicalRankBlock_balanced_affinePerturbation_count_after_equiv r k α e














theorem fixedQuadraticAffine_balancedParam_count_of_transportData
    (n r k : ℕ)
    (q : (Fin n → ZMod 2) → ZMod 2)
    (e : (Fin n → ZMod 2) ≃ (Fin r → ZMod 2 × ZMod 2) × (Fin k → ZMod 2))
    (paramEquiv :
      ((Fin n → ZMod 2) × ZMod 2) ≃
        (Fin r → ZMod 2) × (Fin r → ZMod 2) × (Fin k → ZMod 2) × ZMod 2)
    (htransport : ∀ b : (Fin n → ZMod 2) × ZMod 2,
      ((Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if q x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0
        then (1 : ℤ) else (-1 : ℤ))) = 0) ↔
      ((Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin r =>
              ((e x).1 i).1 * ((e x).1 i).2 +
                (paramEquiv b).1 i * ((e x).1 i).1 +
                (paramEquiv b).2.1 i * ((e x).1 i).2) +
              (paramEquiv b).2.2.2) +
            Finset.univ.sum (fun j : Fin k =>
              (paramEquiv b).2.2.1 j * (e x).2 j) = 0
        then (1 : ℤ) else (-1 : ℤ))) = 0)) :
    Fintype.card {b : (Fin n → ZMod 2) × ZMod 2 //
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if q x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0
        then (1 : ℤ) else (-1 : ℤ))) = 0}
      = 2 ^ (2 * r + 1) * (2 ^ k - 1) := by
  let P : ((Fin n → ZMod 2) × ZMod 2) → Prop := fun b =>
    (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if q x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0
      then (1 : ℤ) else (-1 : ℤ))) = 0
  exact
    balancedParam_count_of_canonicalTransport r k (Fin n → ZMod 2)
      ((Fin n → ZMod 2) × ZMod 2) e paramEquiv P htransport






theorem half_rank_fiber_sum_eq_card_mul_weight
    (n : ℕ) (ι : Type*) [Fintype ι]
    (halfRank : ι → Fin (n + 1)) (w : Fin (n + 1) → ℕ)
    (s : Fin (n + 1)) :
    (∑ a : {a : ι // halfRank a = s}, w (halfRank a.1)) =
      Fintype.card {a : ι // halfRank a = s} * w s := by
  classical
  calc
    (∑ a : {a : ι // halfRank a = s}, w (halfRank a.1))
        = ∑ a : {a : ι // halfRank a = s}, w s := by
          apply Finset.sum_congr
          · rfl
          · intro a ha
            exact congrArg w a.property
    _ = Fintype.card {a : ι // halfRank a = s} * w s := by
          simp




theorem half_rank_sum_eq_sum_fiber_sums
    (n : ℕ) (ι : Type*) [Fintype ι]
    (halfRank : ι → Fin (n + 1)) (w : Fin (n + 1) → ℕ) :
    (∑ a : ι, w (halfRank a)) =
      ∑ s : Fin (n + 1),
        ∑ a : {a : ι // halfRank a = s}, w (halfRank a.1) := by
  classical
  let e : (Sigma fun s : Fin (n + 1) => {a : ι // halfRank a = s}) ≃ ι :=
    { toFun := fun x => x.2.1
      invFun := fun a => ⟨halfRank a, ⟨a, rfl⟩⟩
      left_inv := by
        intro x
        rcases x with ⟨s, a, ha⟩
        cases ha
        rfl
      right_inv := by
        intro a
        rfl }
  simpa [e, Fintype.sum_sigma] using
    (Equiv.sum_comp e (fun a : ι => w (halfRank a))).symm




theorem rankWeight_sum_grouped_by_halfRankFiber
    (n : ℕ) (ι : Type*) [Fintype ι]
    (halfRank : ι → Fin (n + 1)) :
    (∑ a : ι,
        2 ^ (2 * (halfRank a : ℕ) + 1) *
          (2 ^ (n - 2 * (halfRank a : ℕ)) - 1)) =
      ∑ s : Fin (n + 1),
        Fintype.card {a : ι // halfRank a = s} *
          (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)) := by
  classical
  let w : Fin (n + 1) → ℕ := fun s =>
    2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)
  calc
    (∑ a : ι,
        2 ^ (2 * (halfRank a : ℕ) + 1) *
          (2 ^ (n - 2 * (halfRank a : ℕ)) - 1)) =
        ∑ a : ι, w (halfRank a) := by
          rfl
    _ = ∑ s : Fin (n + 1),
          ∑ a : {a : ι // halfRank a = s}, w (halfRank a.1) := by
          exact half_rank_sum_eq_sum_fiber_sums n ι halfRank w
    _ = ∑ s : Fin (n + 1),
          Fintype.card {a : ι // halfRank a = s} * w s := by
          exact Finset.sum_congr rfl (fun s _ =>
            half_rank_fiber_sum_eq_card_mul_weight n ι halfRank w s)
    _ = ∑ s : Fin (n + 1),
          Fintype.card {a : ι // halfRank a = s} *
            (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)) := by
          rfl








theorem nonzeroQuadratic_rankWeight_sum_grouped_by_halfRankFiber_narrow
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} → Fin (n + 1)) :
    (∑ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        2 ^ (2 * (halfRank Q : ℕ) + 1) *
          (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1)) =
      ∑ s : Fin (n + 1),
        Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            halfRank Q = s} *
          (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)) := by
  exact rankWeight_sum_grouped_by_halfRankFiber n
    {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0}
    halfRank










theorem nonzeroQuadratic_rankWeight_sum_grouped_by_halfRankFiber_add_affine
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} → Fin (n + 1)) :
    (∑ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        2 ^ (2 * (halfRank Q : ℕ) + 1) *
          (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1)) + 2 * (2 ^ n - 1) =
      (∑ s : Fin (n + 1),
        Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            halfRank Q = s} *
          (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))) + 2 * (2 ^ n - 1) := by
  exact congrArg (fun x => x + 2 * (2 ^ n - 1))
      (nonzeroQuadratic_rankWeight_sum_grouped_by_halfRankFiber_narrow n halfRank)












theorem linear_delta_sum_add
    (n : ℕ)
    (l l' : Fin n → ZMod 2) (x : Fin n → ZMod 2) :
    (Finset.univ.sum (fun i : Fin n => (l i + l' i) * x i)) =
      (Finset.univ.sum (fun i : Fin n => l i * x i)) +
      (Finset.univ.sum (fun i : Fin n => l' i * x i)) := by
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]






theorem quadraticANF_delta_eval_split
    (n : ℕ)
    (Q Q' : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (l l' : Fin n → ZMod 2) (c c' : ZMod 2)
    (x : Fin n → ZMod 2) :
    (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          (Q i j + Q' i j) * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n => (l i + l' i) * x i) + (c + c')) =
      (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            Q i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => l i * x i) + c) +
        (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            Q' i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => l' i * x i) + c') := by
  have hquad :
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          (Q i j + Q' i j) * x i * x j.1)) =
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            Q i j * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            Q' i j * x i * x j.1)) := by
    simp_rw [add_mul]
    simp_rw [Finset.sum_add_distrib]
  have hlin :
      (Finset.univ.sum (fun i : Fin n => (l i + l' i) * x i)) =
        (Finset.univ.sum (fun i : Fin n => l i * x i)) +
        (Finset.univ.sum (fun i : Fin n => l' i * x i)) :=
    linear_delta_sum_add n l l' x
  rw [hquad, hlin]
  ring




theorem quadraticANF_eval_eq_implies_coeff_eq
    (n : ℕ)
    (Q Q' : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (l l' : Fin n → ZMod 2) (c c' : ZMod 2)
    (hEval : ∀ x : Fin n → ZMod 2,
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          Q i j * x i * x j.1))) +
        Finset.univ.sum (fun i : Fin n => l i * x i) + c =
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          Q' i j * x i * x j.1))) +
        Finset.univ.sum (fun i : Fin n => l' i * x i) + c') :
    Q = Q' ∧ l = l' ∧ c = c' := by
  classical
  have hzero : ∀ x : Fin n → ZMod 2,
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          (Q i j + Q' i j) * x i * x j.1))) +
        Finset.univ.sum (fun i : Fin n => (l i + l' i) * x i) + (c + c') = 0 := by
    intro x
    rw [quadraticANF_delta_eval_split n Q Q' l l' c c' x, hEval x]
    exact zmodTwo_add_self_eq_zero _
  have hcoeff :=
    quadraticANF_zero_eval_coefficients_zero n
      (fun i : Fin n => fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} => Q i j + Q' i j)
      (fun i : Fin n => l i + l' i) (c + c') hzero
  exact eq_of_delta_coefficients_zero n Q Q' l l' c c' hcoeff.1 hcoeff.2.1 hcoeff.2.2




theorem leading_bit_tail_extension_balanced
    (n : ℕ) (g : SymBoolFun n) :
    BalancedByWalsh
      ((fun y : F2Vec (n + 1) => y 0 + g (Fin.tail y)) : SymBoolFun (n + 1)) := by
  classical
  unfold BalancedByWalsh Walsh
  change
    (∑ x : F2Vec (n + 1),
        BitToSign ((x 0 + g (Fin.tail x)) + DotF2 x 0)) = 0
  have zmod2_univ : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext bit
    constructor
    · intro _
      fin_cases bit <;> decide
    · intro _
      exact Finset.mem_univ bit
  have bit_sum_zero (a : ZMod 2) :
      (∑ bit : ZMod 2, BitToSign (bit + a)) = 0 := by
    rw [zmod2_univ]
    fin_cases a <;> native_decide
  let split : F2Vec (n + 1) ≃ F2Vec n × ZMod 2 :=
    { toFun := fun x => (Fin.tail x, x 0)
      invFun := fun p => Fin.cons p.2 p.1
      left_inv := by
        intro x
        exact Fin.cons_self_tail x
      right_inv := by
        intro p
        cases p with
        | mk tail bit =>
            simp [Fin.tail_cons, Fin.cons_zero] }
  calc
    (∑ x : F2Vec (n + 1),
        BitToSign ((x 0 + g (Fin.tail x)) + DotF2 x 0))
        = ∑ p : F2Vec n × ZMod 2, BitToSign (p.2 + g p.1) := by
          apply Fintype.sum_equiv split
          intro x
          simp [split, DotF2]
    _ = ∑ tail : F2Vec n, ∑ bit : ZMod 2, BitToSign (bit + g tail) := by
          simpa using
            (Fintype.sum_prod_type
              (fun p : F2Vec n × ZMod 2 => BitToSign (p.2 + g p.1)))
    _ = 0 := by
          simp [bit_sum_zero]














theorem quadraticANF_cardValue_groupedHalfRank_of_rankWeight_add_affine
    (n : ℕ)
    (value : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hvalue :
      value =
        (∑ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
          2 ^ (2 * (halfRank Q : ℕ) + 1) *
            (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1)) +
          2 * (2 ^ n - 1)) :
    value =
      (∑ s : Fin (n + 1),
        Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            halfRank Q = s} *
          (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))) +
        2 * (2 ^ n - 1) := by
  exact hvalue.trans
    (nonzeroQuadratic_rankWeight_sum_grouped_by_halfRankFiber_add_affine n halfRank)


theorem quadraticANF_balancedCoeff_card_grouped_of_rankWeight_count
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hcount :
      Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0}
        =
        (∑ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
          2 ^ (2 * (halfRank Q : ℕ) + 1) *
            (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1)) +
          2 * (2 ^ n - 1)) :
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0}
      =
    (∑ s : Fin (n + 1),
      Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          halfRank Q = s} *
        (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))) +
      2 * (2 ^ n - 1) := by
  exact quadraticANF_cardValue_groupedHalfRank_of_rankWeight_add_affine n
    (Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0})
    halfRank hcount
















theorem quadraticANF_balancedCoeff_card_closed_of_rankWeight_count_and_closed_fibers
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (fiberCount : Fin (n + 1) → ℕ)
    (hcount :
      Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0}
        =
        (∑ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
          2 ^ (2 * (halfRank Q : ℕ) + 1) *
            (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1)) +
          2 * (2 ^ n - 1))
    (hfiber : ∀ s : Fin (n + 1),
      Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            halfRank Q = s} = fiberCount s) :
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0}
      =
      (∑ s : Fin (n + 1),
        fiberCount s *
          (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))) +
        2 * (2 ^ n - 1) := by
  simpa [hfiber] using
      quadraticANF_balancedCoeff_card_grouped_of_rankWeight_count n halfRank hcount




















theorem quadraticFamily_balancedAffineParam_sigma_count_of_transportData
    (n : ℕ) (ι : Type*) [Fintype ι]
    (r k : ι → ℕ)
    (q : ι → (Fin n → ZMod 2) → ZMod 2)
    (e : ∀ a : ι,
      (Fin n → ZMod 2) ≃
        (Fin (r a) → ZMod 2 × ZMod 2) × (Fin (k a) → ZMod 2))
    (paramEquiv : ∀ a : ι,
      ((Fin n → ZMod 2) × ZMod 2) ≃
        (Fin (r a) → ZMod 2) × (Fin (r a) → ZMod 2) ×
          (Fin (k a) → ZMod 2) × ZMod 2)
    (htransport : ∀ (a : ι) (b : (Fin n → ZMod 2) × ZMod 2),
      ((Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0
        then (1 : ℤ) else (-1 : ℤ))) = 0) ↔
      ((Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin (r a) =>
              (((e a) x).1 i).1 * (((e a) x).1 i).2 +
                ((paramEquiv a) b).1 i * (((e a) x).1 i).1 +
                ((paramEquiv a) b).2.1 i * (((e a) x).1 i).2) +
              ((paramEquiv a) b).2.2.2) +
            Finset.univ.sum (fun j : Fin (k a) =>
              ((paramEquiv a) b).2.2.1 j * (((e a) x).2 j)) = 0
        then (1 : ℤ) else (-1 : ℤ))) = 0)) :
    Fintype.card
      (Σ a : ι, {b : (Fin n → ZMod 2) × ZMod 2 //
        (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0
          then (1 : ℤ) else (-1 : ℤ))) = 0}) =
    ∑ a : ι, 2 ^ (2 * r a + 1) * (2 ^ k a - 1) := by
  let S : ι → Type _ := fun a =>
    {b : (Fin n → ZMod 2) × ZMod 2 //
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0
        then (1 : ℤ) else (-1 : ℤ))) = 0}
  have hfiber : ∀ a : ι,
      Fintype.card (S a) = 2 ^ (2 * r a + 1) * (2 ^ k a - 1) := by
    intro a
    change Fintype.card {b : (Fin n → ZMod 2) × ZMod 2 //
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0
        then (1 : ℤ) else (-1 : ℤ))) = 0} =
      2 ^ (2 * r a + 1) * (2 ^ k a - 1)
    exact fixedQuadraticAffine_balancedParam_count_of_transportData
      n (r a) (k a) (q a) (e a) (paramEquiv a) (htransport a)
  change Fintype.card (Sigma S) = ∑ a : ι, 2 ^ (2 * r a + 1) * (2 ^ k a - 1)
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun a _ => hfiber a)




theorem quadraticANF_nonzeroBalancedCoeff_card_eq_transportData_sum_of_nonzeroEquiv (n : ℕ) (ι : Type*) [Fintype ι] (r k : ι → ℕ) (q : ι → (Fin n → ZMod 2) → ZMod 2) (e : ∀ a : ι, (Fin n → ZMod 2) ≃ (Fin (r a) → ZMod 2 × ZMod 2) × (Fin (k a) → ZMod 2)) (paramEquiv : ∀ a : ι, ((Fin n → ZMod 2) × ZMod 2) ≃ (Fin (r a) → ZMod 2) × (Fin (r a) → ZMod 2) × (Fin (k a) → ZMod 2) × ZMod 2) (htransport : ∀ (a : ι) (b : (Fin n → ZMod 2) × ZMod 2), (Finset.univ.sum (fun x : Fin n → ZMod 2 => if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then (1 : ℤ) else (-1 : ℤ)) = 0) ↔ (Finset.univ.sum (fun x : Fin n → ZMod 2 => if (Finset.univ.sum (fun i : Fin (r a) => (((e a) x).1 i).1 * (((e a) x).1 i).2 + ((paramEquiv a) b).1 i * (((e a) x).1 i).1 + ((paramEquiv a) b).2.1 i * (((e a) x).1 i).2) + ((paramEquiv a) b).2.2.2) + Finset.univ.sum (fun j : Fin (k a) => ((paramEquiv a) b).2.2.1 j * (((e a) x).2 j)) = 0 then (1 : ℤ) else (-1 : ℤ)) = 0)) (nonzeroEquiv : {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) // p.1 ≠ 0 ∧ Finset.univ.sum (fun x : Fin n → ZMod 2 => if Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} => p.1 i j * x i * x j.1)) + Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then (1 : ℤ) else (-1 : ℤ)) = 0} ≃ (Σ a : ι, {b : (Fin n → ZMod 2) × ZMod 2 // Finset.univ.sum (fun x : Fin n → ZMod 2 => if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then (1 : ℤ) else (-1 : ℤ)) = 0})) : Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) // p.1 ≠ 0 ∧ Finset.univ.sum (fun x : Fin n → ZMod 2 => if Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} => p.1 i j * x i * x j.1)) + Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then (1 : ℤ) else (-1 : ℤ)) = 0} = ∑ a : ι, 2 ^ (2 * r a + 1) * (2 ^ k a - 1) := by
  calc
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) // p.1 ≠ 0 ∧ Finset.univ.sum (fun x : Fin n → ZMod 2 => if Finset.univ.sum (fun i : Fin n => Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} => p.1 i j * x i * x j.1)) + Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then (1 : ℤ) else (-1 : ℤ)) = 0}
        = Fintype.card (Σ a : ι, {b : (Fin n → ZMod 2) × ZMod 2 // Finset.univ.sum (fun x : Fin n → ZMod 2 => if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then (1 : ℤ) else (-1 : ℤ)) = 0}) := by
          exact Fintype.card_congr nonzeroEquiv
    _ = ∑ a : ι, 2 ^ (2 * r a + 1) * (2 ^ k a - 1) := by
          exact quadraticFamily_balancedAffineParam_sigma_count_of_transportData n ι r k q e paramEquiv htransport












theorem zero_quadratic_signed_sum_affine
    (n : ℕ)
    (p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2))
    (hquad : p.1 = 0) :
    Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            p.1 i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
        (1 : ℤ)
      else
        (-1 : ℤ)) =
    Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if (Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
        (1 : ℤ)
      else
        (-1 : ℤ)) := by
  classical
  simp [hquad]




theorem quadraticANF_zeroQuadratic_signedSum_zero_iff_affine
    (n : ℕ)
    (p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2))
    (hquad : p.1 = 0) :
    (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            p.1 i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0) ↔
    (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if (Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0) := by
  rw [zero_quadratic_signed_sum_affine n p hquad]












theorem quadraticANF_zeroQuadratic_balancedCoeff_card_closed_from_iff
    (n : ℕ) :
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 = 0 ∧
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)}
      = 2 * (2 ^ n - 1) := by
  let e : {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 = 0 ∧
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)} ≃
      {p : (Fin n → ZMod 2) × ZMod 2 //
        (∑ x : Fin n → ZMod 2,
          (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0} :=
    { toFun := fun p =>
        ⟨(p.1.2.1, p.1.2.2), by
          exact (quadraticANF_zeroQuadratic_signedSum_zero_iff_affine n p.1 p.2.1).mp p.2.2⟩
      invFun := fun p =>
        ⟨(0, p.1.1, p.1.2), by
          constructor
          · rfl
          · exact (quadraticANF_zeroQuadratic_signedSum_zero_iff_affine n (0, p.1.1, p.1.2) rfl).mpr p.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        cases p with
        | mk val h =>
          cases val with
          | mk quad affine =>
            cases h.1
            rfl
      right_inv := by
        intro p
        apply Subtype.ext
        rfl }
  calc
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 = 0 ∧
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)}
        = Fintype.card {p : (Fin n → ZMod 2) × ZMod 2 //
            (∑ x : Fin n → ZMod 2,
              (if Finset.univ.sum (fun i : Fin n => p.1 i * x i) + p.2 = 0
               then (1 : ℤ) else (-1 : ℤ))) = 0} := Fintype.card_congr e
    _ = 2 * (2 ^ n - 1) := balancedAffine_signedSum_count n






theorem quadraticANF_balancedCoeff_card_eq_nonzeroQuadratic_add_affine
    (n : ℕ) :
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)}
      =
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 ≠ 0 ∧
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)}
      + 2 * (2 ^ n - 1) := by
  classical
  let C : Type := (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2)
  let BalancedCoeff : C → Prop := fun p =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0
  let AllBalanced : Type := {p : C // BalancedCoeff p}
  let ZeroBalanced : Type := {p : C // p.1 = 0 ∧ BalancedCoeff p}
  let NonzeroBalanced : Type := {p : C // p.1 ≠ 0 ∧ BalancedCoeff p}
  have hpartition : Fintype.card AllBalanced =
      Fintype.card ZeroBalanced + Fintype.card NonzeroBalanced := by
    let e : AllBalanced ≃ (ZeroBalanced ⊕ NonzeroBalanced) := {
      toFun := fun p =>
        if hp : p.1.1 = 0 then
          Sum.inl ⟨p.1, And.intro hp p.2⟩
        else
          Sum.inr ⟨p.1, And.intro hp p.2⟩
      invFun := fun q =>
        match q with
        | Sum.inl p => ⟨p.1, p.2.2⟩
        | Sum.inr p => ⟨p.1, p.2.2⟩
      left_inv := by
        intro p
        by_cases hp : p.1.1 = 0
        · simp [hp]
        · simp [hp]
      right_inv := by
        intro q
        cases q with
        | inl p =>
            simp [p.2.1]
        | inr p =>
            simp [p.2.1] }
    simpa [Fintype.card_sum] using (Fintype.card_congr e)
  have hzero : Fintype.card ZeroBalanced = 2 * (2 ^ n - 1) := by
    change Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 = 0 ∧
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)} = 2 * (2 ^ n - 1)
    exact quadraticANF_zeroQuadratic_balancedCoeff_card_closed_from_iff n
  have hmain : Fintype.card AllBalanced =
      Fintype.card NonzeroBalanced + 2 * (2 ^ n - 1) := by
    calc
      Fintype.card AllBalanced =
          Fintype.card ZeroBalanced + Fintype.card NonzeroBalanced := hpartition
      _ = Fintype.card NonzeroBalanced + Fintype.card ZeroBalanced := by
            rw [Nat.add_comm]
      _ = Fintype.card NonzeroBalanced + 2 * (2 ^ n - 1) := by
            rw [hzero]
  exact hmain




theorem quadraticANF_balancedCoeff_card_eq_nonzeroQuadratic_add_affine_closed
    (n : ℕ) :
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)}
      =
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 ≠ 0 ∧
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0)}
      + 2 * (2 ^ n - 1) := by
  exact quadraticANF_balancedCoeff_card_eq_nonzeroQuadratic_add_affine n




theorem quadraticANF_balancedCoeff_card_eq_transportData_sum_add_affine
    (n : ℕ) (ι : Type*) [Fintype ι]
    (r k : ι → ℕ)
    (q : ι → (Fin n → ZMod 2) → ZMod 2)
    (e : ∀ a : ι,
      (Fin n → ZMod 2) ≃
        (Fin (r a) → ZMod 2 × ZMod 2) × (Fin (k a) → ZMod 2))
    (paramEquiv : ∀ a : ι,
      ((Fin n → ZMod 2) × ZMod 2) ≃
        (Fin (r a) → ZMod 2) × (Fin (r a) → ZMod 2) ×
          (Fin (k a) → ZMod 2) × ZMod 2)
    (htransport : ∀ (a : ι) (b : (Fin n → ZMod 2) × ZMod 2),
      (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0) ↔
        (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if (Finset.univ.sum
                  (fun i : Fin (r a) =>
                    (((e a) x).1 i).1 * (((e a) x).1 i).2 +
                      ((paramEquiv a) b).1 i * (((e a) x).1 i).1 +
                        ((paramEquiv a) b).2.1 i * (((e a) x).1 i).2) +
                  ((paramEquiv a) b).2.2.2) +
                Finset.univ.sum
                  (fun j : Fin (k a) =>
                    ((paramEquiv a) b).2.2.1 j * ((e a) x).2 j) = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0))
    (nonzeroEquiv :
      {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        p.1 ≠ 0 ∧
          Finset.univ.sum
              (fun x : Fin n → ZMod 2 =>
                if Finset.univ.sum
                        (fun i : Fin n =>
                          Finset.univ.sum
                            (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                              p.1 i j * x i * x j.1)) +
                      Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0} ≃
        (Σ a : ι,
          {b : (Fin n → ZMod 2) × ZMod 2 //
            Finset.univ.sum
                (fun x : Fin n → ZMod 2 =>
                  if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0})) :
    Fintype.card
      {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        Finset.univ.sum
            (fun x : Fin n → ZMod 2 =>
              if Finset.univ.sum
                      (fun i : Fin n =>
                        Finset.univ.sum
                          (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                            p.1 i j * x i * x j.1)) +
                    Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
                (1 : ℤ)
              else
                (-1 : ℤ)) = 0}
      =
    (∑ a : ι, 2 ^ (2 * (r a) + 1) * (2 ^ (k a) - 1)) + 2 * (2 ^ n - 1) := by
  rw [quadraticANF_balancedCoeff_card_eq_nonzeroQuadratic_add_affine_closed n]
  rw [quadraticANF_nonzeroBalancedCoeff_card_eq_transportData_sum_of_nonzeroEquiv n ι r k q e paramEquiv htransport nonzeroEquiv]




theorem transport_data_instantiated_nonzero_quadratic_sum
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
      (Fin n → ZMod 2) → ZMod 2)
    (e : ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
      (Fin n → ZMod 2) ≃
        (Fin (halfRank Q : ℕ) → ZMod 2 × ZMod 2) ×
          (Fin (n - 2 * (halfRank Q : ℕ)) → ZMod 2))
    (paramEquiv : ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
      ((Fin n → ZMod 2) × ZMod 2) ≃
        (Fin (halfRank Q : ℕ) → ZMod 2) ×
          (Fin (halfRank Q : ℕ) → ZMod 2) ×
            (Fin (n - 2 * (halfRank Q : ℕ)) → ZMod 2) × ZMod 2)
    (htransport : ∀
      (Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0})
      (b : (Fin n → ZMod 2) × ZMod 2),
      (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if q Q x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0) ↔
        (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if (Finset.univ.sum
                  (fun i : Fin (halfRank Q : ℕ) =>
                    (((e Q) x).1 i).1 * (((e Q) x).1 i).2 +
                      ((paramEquiv Q) b).1 i * (((e Q) x).1 i).1 +
                        ((paramEquiv Q) b).2.1 i * (((e Q) x).1 i).2) +
                ((paramEquiv Q) b).2.2.2) +
                Finset.univ.sum
                  (fun j : Fin (n - 2 * (halfRank Q : ℕ)) =>
                    ((paramEquiv Q) b).2.2.1 j * ((e Q) x).2 j) = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0))
    (nonzeroEquiv :
      {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) //
        p.1 ≠ 0 ∧
          Finset.univ.sum
              (fun x : Fin n → ZMod 2 =>
                if Finset.univ.sum
                        (fun i : Fin n =>
                          Finset.univ.sum
                            (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                              p.1 i j * x i * x j.1)) +
                      Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0} ≃
        (Σ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
          {b : (Fin n → ZMod 2) × ZMod 2 //
            Finset.univ.sum
              (fun x : Fin n → ZMod 2 =>
                if q Q x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0})) :
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0}
      =
    (∑ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
      2 ^ (2 * (halfRank Q : ℕ) + 1) *
        (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1)) +
      2 * (2 ^ n - 1) := by
  classical
  exact quadraticANF_balancedCoeff_card_eq_transportData_sum_add_affine
    n
    {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0}
    (fun Q => (halfRank Q : ℕ))
    (fun Q => n - 2 * (halfRank Q : ℕ))
    q e paramEquiv htransport nonzeroEquiv




theorem half_rank_grouping_for_nonzero_quadratic_weight_sum
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1)) :
    (∑ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
      2 ^ (2 * (halfRank Q : ℕ) + 1) *
        (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1)) +
      2 * (2 ^ n - 1)
      =
    (∑ s : Fin (n + 1),
      Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          halfRank Q = s} *
        (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))) +
      2 * (2 ^ n - 1) := by
  classical
  exact nonzeroQuadratic_rankWeight_sum_grouped_by_halfRankFiber_add_affine n halfRank


















theorem quadraticANF_eval_eq_implies_packed_coeff_eq
    (n : ℕ)
    (p p' : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2)
    (hEval : ∀ x : Fin n → ZMod 2,
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          p.1 i j * x i * x j.1))) +
        Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 =
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          p'.1 i j * x i * x j.1))) +
        Finset.univ.sum (fun i : Fin n => p'.2.1 i * x i) + p'.2.2) :
    p = p' := by
  rcases p with ⟨Q, lc⟩
  rcases lc with ⟨l, c⟩
  rcases p' with ⟨Q', l'c'⟩
  rcases l'c' with ⟨l', c'⟩
  have hCoeff :=
    quadraticANF_eval_eq_implies_coeff_eq n Q Q' l l' c c' hEval
  rcases hCoeff with ⟨hQ, hl, hc⟩
  cases hQ
  cases hl
  cases hc
  rfl




theorem quadraticANF_evalMap_injective_packed_from_recovery
    (n : ℕ) :
    Function.Injective
      (fun p : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2 =>
        (fun x : Fin n → ZMod 2 =>
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2))) := by
  intro p p' h
  exact quadraticANF_eval_eq_implies_packed_coeff_eq n p p' (fun x => congrFun h x)




theorem quadraticANF_evalMap_subtype_injective_from_packed
    (n : ℕ)
    (P : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) → Prop) :
    Function.Injective
      (fun q : {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) // P p} =>
        (fun x : Fin n → ZMod 2 =>
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              q.1.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => q.1.2.1 i * x i) + q.1.2.2))) := by
  intro q r h
  apply Subtype.ext
  exact quadraticANF_evalMap_injective_packed_from_recovery n h




















theorem quadraticANF_balancedCoeff_evalRange_card_eq
    (n : ℕ) :
    (let Coeff :=
      (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2);
     let Balanced : Coeff → Prop := (fun p =>
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0));
     let Eval : {p : Coeff // Balanced p} → ((Fin n → ZMod 2) → ZMod 2) := (fun q =>
      fun x : Fin n → ZMod 2 =>
        (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            q.1.1 i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => q.1.2.1 i * x i) + q.1.2.2));
     Fintype.card (Set.range Eval) = Fintype.card {p : Coeff // Balanced p}) := by
  classical
  let Coeff :=
    (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
      (Fin n → ZMod 2) × ZMod 2)
  let Balanced : Coeff → Prop := (fun p =>
    (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            p.1 i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0))
  let Eval : {p : Coeff // Balanced p} → ((Fin n → ZMod 2) → ZMod 2) := (fun q =>
    fun x : Fin n → ZMod 2 =>
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          q.1.1 i j * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n => q.1.2.1 i * x i) + q.1.2.2))
  have hEval : Function.Injective Eval := by
    simpa [Eval, Coeff] using
      (quadraticANF_evalMap_subtype_injective_from_packed n Balanced)
  let evalEmbedding : {p : Coeff // Balanced p} ↪ ((Fin n → ZMod 2) → ZMod 2) :=
    ⟨Eval, hEval⟩
  change Fintype.card (Set.range Eval) = Fintype.card {p : Coeff // Balanced p}
  simpa [evalEmbedding] using (Fintype.card_range evalEmbedding)
























theorem quadraticANF_balancedEvalRange_card_eq_transportData_sum_add_affine
    (n : ℕ) (ι : Type*) [Fintype ι]
    (r k : ι → ℕ)
    (q : ι → (Fin n → ZMod 2) → ZMod 2)
    (e : ∀ a : ι,
      (Fin n → ZMod 2) ≃
        (Fin (r a) → ZMod 2 × ZMod 2) × (Fin (k a) → ZMod 2))
    (paramEquiv : ∀ a : ι,
      ((Fin n → ZMod 2) × ZMod 2) ≃
        (Fin (r a) → ZMod 2) × (Fin (r a) → ZMod 2) ×
          (Fin (k a) → ZMod 2) × ZMod 2)
    (htransport : ∀ (a : ι) (b : (Fin n → ZMod 2) × ZMod 2),
      (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0) ↔
        (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if (Finset.univ.sum
                  (fun i : Fin (r a) =>
                    (((e a) x).1 i).1 * (((e a) x).1 i).2 +
                      ((paramEquiv a) b).1 i * (((e a) x).1 i).1 +
                        ((paramEquiv a) b).2.1 i * (((e a) x).1 i).2) +
                    ((paramEquiv a) b).2.2.2) +
                  Finset.univ.sum
                    (fun j : Fin (k a) => ((paramEquiv a) b).2.2.1 j * ((e a) x).2 j) = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0))
    (nonzeroEquiv :
      {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) //
        p.1 ≠ 0 ∧
          Finset.univ.sum
              (fun x : Fin n → ZMod 2 =>
                if Finset.univ.sum
                        (fun i : Fin n =>
                          Finset.univ.sum
                            (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                              p.1 i j * x i * x j.1)) +
                      Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0} ≃
        (Σ a : ι,
          {b : (Fin n → ZMod 2) × ZMod 2 //
            Finset.univ.sum
                (fun x : Fin n → ZMod 2 =>
                  if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0})) :
    (let Coeff :=
      (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2);
     let Balanced : Coeff → Prop := fun p =>
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0);
     let Eval : {p : Coeff // Balanced p} → ((Fin n → ZMod 2) → ZMod 2) := fun s =>
      fun x : Fin n → ZMod 2 =>
        (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            s.1.1 i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => s.1.2.1 i * x i) + s.1.2.2);
     Fintype.card (Set.range Eval) =
      (∑ a : ι, 2 ^ (2 * (r a) + 1) * (2 ^ (k a) - 1)) + 2 * (2 ^ n - 1)) := by
  exact (quadraticANF_balancedCoeff_evalRange_card_eq n).trans
    (quadraticANF_balancedCoeff_card_eq_transportData_sum_add_affine
      n ι r k q e paramEquiv htransport nonzeroEquiv)




theorem quadraticANF_balancedEvalRange_card_eq_nonzeroQuadratic_transportData_sum_add_affine
    (n : ℕ) :
    (let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let NonzeroQuad := {Q : Quad // Q ≠ 0};
     let quadEvalRaw : Quad → (Fin n → ZMod 2) → ZMod 2 := fun Q x =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          Q i j * x i * x j.1));
     ∀ (r k : NonzeroQuad → ℕ)
       (e : ∀ Q : NonzeroQuad,
          (Fin n → ZMod 2) ≃
            (Fin (r Q) → ZMod 2 × ZMod 2) × (Fin (k Q) → ZMod 2))
       (paramEquiv : ∀ Q : NonzeroQuad,
          ((Fin n → ZMod 2) × ZMod 2) ≃
            (Fin (r Q) → ZMod 2) × (Fin (r Q) → ZMod 2) ×
              (Fin (k Q) → ZMod 2) × ZMod 2)
       (_htransport : ∀ (Q : NonzeroQuad) (b : (Fin n → ZMod 2) × ZMod 2),
          (Finset.univ.sum
              (fun x : Fin n → ZMod 2 =>
                if quadEvalRaw Q.1 x +
                    Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0) ↔
            (Finset.univ.sum
              (fun x : Fin n → ZMod 2 =>
                if (Finset.univ.sum
                      (fun i : Fin (r Q) =>
                        (((e Q) x).1 i).1 * (((e Q) x).1 i).2 +
                          ((paramEquiv Q) b).1 i * (((e Q) x).1 i).1 +
                          ((paramEquiv Q) b).2.1 i * (((e Q) x).1 i).2) +
                      ((paramEquiv Q) b).2.2.2) +
                    Finset.univ.sum
                      (fun j : Fin (k Q) =>
                        ((paramEquiv Q) b).2.2.1 j * ((e Q) x).2 j) = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0)),
       (let Coeff := Quad × (Fin n → ZMod 2) × ZMod 2;
        let Balanced : Coeff → Prop := fun p =>
          (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
            if quadEvalRaw p.1 x +
                Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0);
        let Eval : {p : Coeff // Balanced p} → ((Fin n → ZMod 2) → ZMod 2) := fun q =>
          fun x : Fin n → ZMod 2 =>
            quadEvalRaw q.1.1 x +
              Finset.univ.sum (fun i : Fin n => q.1.2.1 i * x i) + q.1.2.2;
        Fintype.card (Set.range Eval)) =
       (∑ Q : NonzeroQuad,
          2 ^ (2 * (r Q) + 1) * (2 ^ (k Q) - 1)) + 2 * (2 ^ n - 1)) := by
  dsimp only
  intro r k e paramEquiv htransport
  let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2
  let NonzeroQuad := {Q : Quad // Q ≠ 0}
  let qRaw : Quad → (Fin n → ZMod 2) → ZMod 2 := fun Q x =>
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
        Q i j * x i * x j.1))
  let fullBalanced : Quad × (Fin n → ZMod 2) × ZMod 2 → Prop := fun p =>
    Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if qRaw p.1 x + Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0
  let branchBalanced : NonzeroQuad → ((Fin n → ZMod 2) × ZMod 2) → Prop := fun Q b =>
    Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if qRaw Q.1 x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0
  let nonzeroEquiv :
      {p : Quad × (Fin n → ZMod 2) × ZMod 2 // p.1 ≠ 0 ∧ fullBalanced p} ≃
        (Σ Q : NonzeroQuad, {b : (Fin n → ZMod 2) × ZMod 2 // branchBalanced Q b}) :=
    { toFun := fun p =>
        ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun s =>
        ⟨(s.1.1, s.2.1), ⟨s.1.2, s.2.2⟩⟩
      left_inv := by
        intro p
        cases p with
        | mk val property =>
          cases val with
          | mk Q b =>
            cases property with
            | intro hQ hb =>
              rfl
      right_inv := by
        intro s
        cases s with
        | mk Q b =>
          cases Q with
          | mk Q hQ =>
            cases b with
            | mk b hb =>
              rfl }
  simpa [Quad, NonzeroQuad, qRaw, fullBalanced, branchBalanced] using
    (quadraticANF_balancedEvalRange_card_eq_transportData_sum_add_affine
      n NonzeroQuad r k (fun Q : NonzeroQuad => qRaw Q.1) e paramEquiv htransport nonzeroEquiv)




theorem quad_eval_raw_zero (n : ℕ) :
    (let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let quadEvalRaw : Quad → (Fin n → ZMod 2) → ZMod 2 := fun Q x =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
          Q i j * x i * x j.1));
     ∀ x : Fin n → ZMod 2, quadEvalRaw 0 x = 0) := by
  dsimp
  intro x
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  simp




theorem balanced_eval_range_split_zero_nonzero
    {X Lin Quad : Type*} [Fintype X] [Zero Quad] [DecidableEq Quad]
    (quadEvalRaw : Quad → X → ZMod 2)
    (linearEval : Lin → X → ZMod 2)
    (hzero : ∀ x : X, quadEvalRaw 0 x = 0) :
    Set.range
      (fun q : {p : Quad × Lin × ZMod 2 //
          Finset.univ.sum (fun x : X =>
            if quadEvalRaw p.1 x + linearEval p.2.1 x + p.2.2 = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0} =>
        fun x : X => quadEvalRaw q.1.1 x + linearEval q.1.2.1 x + q.1.2.2)
      =
    Set.range
      (fun q : {p : Option {Q : Quad // Q ≠ 0} × Lin × ZMod 2 //
          Finset.univ.sum (fun x : X =>
            if (match p.1 with
                | none => 0
                | some Q => quadEvalRaw Q.1 x) +
                linearEval p.2.1 x + p.2.2 = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0} =>
        fun x : X =>
          (match q.1.1 with
            | none => 0
            | some Q => quadEvalRaw Q.1 x) +
            linearEval q.1.2.1 x + q.1.2.2) := by
  classical
  ext f
  constructor
  · intro hf
    rcases hf with ⟨q, rfl⟩
    by_cases hQ : q.1.1 = 0
    · exact
        ⟨⟨(none, q.1.2.1, q.1.2.2),
            by
              simpa [hQ, hzero] using q.2⟩,
          by
            funext x
            simp [hQ, hzero x]⟩
    · exact
        ⟨⟨(some ⟨q.1.1, hQ⟩, q.1.2.1, q.1.2.2),
            by
              simpa using q.2⟩,
          by
            rfl⟩
  · intro hf
    rcases hf with ⟨q, rfl⟩
    cases hopt : q.1.1 with
    | none =>
        exact
          ⟨⟨(0, q.1.2.1, q.1.2.2),
              by
                simpa [hopt, hzero] using q.2⟩,
            by
              funext x
              simp [hopt, hzero x]⟩
    | some Q =>
        exact
          ⟨⟨(Q.1, q.1.2.1, q.1.2.2),
              by
                simpa [hopt] using q.2⟩,
            by
              funext x
              simp [hopt]⟩




theorem card_sub_affine_of_total_eq_add
    (n total nonzero : ℕ)
    (h : total = nonzero + 2 * (2 ^ n - 1)) :
    nonzero = total - 2 * (2 ^ n - 1) := by
  simp [h]




theorem total_eq_nonzero_quadratic_add_affine_from_named_total
    (n total : ℕ)
    (htotal :
      Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0)}
        = total) :
    total =
      (Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        p.1 ≠ 0 ∧
          (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
            if (Finset.univ.sum (fun i : Fin n =>
                Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                  p.1 i j * x i * x j.1)) +
                Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0)}) +
        2 * (2 ^ n - 1) := by
  simpa [htotal] using
    (quadraticANF_balancedCoeff_card_eq_nonzeroQuadratic_add_affine_closed n)














theorem quadraticANF_exactDegreeTwoCoeff_card_eq_closedTotal_sub_affine_of_total
    (n total : ℕ)
    (htotal :
      Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0}
        = total) :
    Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 ≠ 0 ∧
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0}
      = total - 2 * (2 ^ n - 1) := by
  exact card_sub_affine_of_total_eq_add n total
    (Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2) //
      p.1 ≠ 0 ∧
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0})
    (by
      exact htotal.symm.trans (quadraticANF_balancedCoeff_card_eq_nonzeroQuadratic_add_affine_closed n))




theorem nonzero_quadratic_card_eq_balanced_param_sigma_card
    (n : ℕ) (ι : Type*) [Fintype ι]
    (q : ι → (Fin n → ZMod 2) → ZMod 2)
    (nonzeroEquiv :
      {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) //
        p.1 ≠ 0 ∧
          Finset.univ.sum
              (fun x : Fin n → ZMod 2 =>
                if Finset.univ.sum
                        (fun i : Fin n =>
                          Finset.univ.sum
                            (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                              p.1 i j * x i * x j.1)) +
                      Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0} ≃
        (Σ a : ι,
          {b : (Fin n → ZMod 2) × ZMod 2 //
            Finset.univ.sum
                (fun x : Fin n → ZMod 2 =>
                  if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0})) :
    Fintype.card
        {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) × (Fin n → ZMod 2) × ZMod 2) //
          p.1 ≠ 0 ∧
            Finset.univ.sum
                (fun x : Fin n → ZMod 2 =>
                  if Finset.univ.sum
                          (fun i : Fin n =>
                            Finset.univ.sum
                              (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                                p.1 i j * x i * x j.1)) +
                        Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0} =
      Fintype.card
        (Σ a : ι,
          {b : (Fin n → ZMod 2) × ZMod 2 //
            Finset.univ.sum
                (fun x : Fin n → ZMod 2 =>
                  if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0}) := by
  exact Fintype.card_congr nonzeroEquiv




theorem balanced_param_sigma_card_eq_transport_sum
    (n : ℕ) (ι : Type*) [Fintype ι]
    (r k : ι → ℕ)
    (q : ι → (Fin n → ZMod 2) → ZMod 2)
    (e : ∀ a : ι, (Fin n → ZMod 2) ≃ (Fin (r a) → ZMod 2 × ZMod 2) × (Fin (k a) → ZMod 2))
    (paramEquiv : ∀ a : ι,
      ((Fin n → ZMod 2) × ZMod 2) ≃
        (Fin (r a) → ZMod 2) × (Fin (r a) → ZMod 2) × (Fin (k a) → ZMod 2) × ZMod 2)
    (htransport : ∀ (a : ι) (b : (Fin n → ZMod 2) × ZMod 2),
      (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0) ↔
        (Finset.univ.sum
          (fun x : Fin n → ZMod 2 =>
            if (Finset.univ.sum
                  (fun i : Fin (r a) =>
                    (((e a) x).1 i).1 * (((e a) x).1 i).2 +
                      ((paramEquiv a) b).1 i * (((e a) x).1 i).1 +
                      ((paramEquiv a) b).2.1 i * (((e a) x).1 i).2) +
                ((paramEquiv a) b).2.2.2) +
                Finset.univ.sum
                  (fun j : Fin (k a) =>
                    ((paramEquiv a) b).2.2.1 j * (((e a) x).2 j)) = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ)) = 0)) :
    Fintype.card
        (Σ a : ι,
          {b : (Fin n → ZMod 2) × ZMod 2 //
            Finset.univ.sum
                (fun x : Fin n → ZMod 2 =>
                  if q a x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0}) =
      ∑ a : ι, 2 ^ (2 * r a + 1) * (2 ^ k a - 1) := by
  exact quadraticFamily_balancedAffineParam_sigma_count_of_transportData n ι r k q e paramEquiv htransport




theorem tail_extension_subtype_eq_implies_tail_eq
    (n : ℕ) (g g' : SymBoolFun n)
    (h :
      (⟨((fun y : F2Vec (n + 1) => y 0 + g (Fin.tail y)) : SymBoolFun (n + 1)),
        leading_bit_tail_extension_balanced n g⟩ :
        {f : SymBoolFun (n + 1) // BalancedByWalsh f}) =
      (⟨((fun y : F2Vec (n + 1) => y 0 + g' (Fin.tail y)) : SymBoolFun (n + 1)),
        leading_bit_tail_extension_balanced n g'⟩ :
        {f : SymBoolFun (n + 1) // BalancedByWalsh f})) :
    g = g' := by
  classical
  funext x
  have hval :
      ((fun y : F2Vec (n + 1) => y 0 + g (Fin.tail y)) : SymBoolFun (n + 1)) =
        ((fun y : F2Vec (n + 1) => y 0 + g' (Fin.tail y)) : SymBoolFun (n + 1)) := by
    exact congrArg Subtype.val h
  have hx := congrFun hval (Fin.cons (0 : ZMod 2) x)
  simpa using hx




theorem quadratic_signed_sum_eq_zero_iff_of_sum_eq
    (n : ℕ)
    (p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2))
    (hsum :
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ))) =
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)))) :
    (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            p.1 i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0) ↔
    (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
      if (Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
        (1 : ℤ)
      else
        (-1 : ℤ)) = 0) := by
  rw [hsum]




theorem upper_triangular_coeff_shape
    (n : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) :
    (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
        fun i j =>
          if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
          else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
          else 0;
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i)) := by
  dsimp
  constructor
  · intro i
    simp
  · intro i j
    by_cases hij : (i : ℕ) < (j : ℕ)
    · have hji : ¬ (j : ℕ) < (i : ℕ) := not_lt_of_gt hij
      simp [hij, hji]
    · by_cases hji : (j : ℕ) < (i : ℕ)
      · have hij' : ¬ (i : ℕ) < (j : ℕ) := not_lt_of_gt hji
        simp [hij', hji]
      · simp [hij, hji]




theorem upper_triangular_coeff_apply_subtype
    (n : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (i : Fin n) (j : {j : Fin n // (i : ℕ) < (j : ℕ)}) :
    ((fun i j : Fin n =>
      if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
      else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
      else 0) : Matrix (Fin n) (Fin n) (ZMod 2)) i j.1 = Q i j := by
  rcases j with ⟨j, hij⟩
  simp [hij]






theorem upperTriangularCoeff_matrix_shape_and_injective
    (n : ℕ) :
    (∀ Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2,
      (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
        fun i j =>
          if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
          else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
          else 0;
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i))) ∧
    Function.Injective
      (fun Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2 =>
        ((fun i j : Fin n =>
          if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
          else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
          else 0) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
  constructor
  · intro Q
    exact upper_triangular_coeff_shape n Q
  · intro Q Q' hQQ'
    funext i j
    have hentry :
        ((fun i j : Fin n =>
          if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
          else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
          else 0) : Matrix (Fin n) (Fin n) (ZMod 2)) i j.1 =
        ((fun i j : Fin n =>
          if h : (i : ℕ) < (j : ℕ) then Q' i ⟨j, h⟩
          else if h : (j : ℕ) < (i : ℕ) then Q' j ⟨i, h⟩
          else 0) : Matrix (Fin n) (Fin n) (ZMod 2)) i j.1 := by
      exact congrFun (congrFun hQQ' i) j.1
    rw [upper_triangular_coeff_apply_subtype n Q i j,
      upper_triangular_coeff_apply_subtype n Q' i j] at hentry
    exact hentry








theorem upperTriangularCoeff_rankFiber_card_eq_alternatingRankStratum
    (n r : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ) :
    Fintype.card {Q : ((i : Fin n) → ({j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)) //
      rank (((fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
        else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
        else 0) : Matrix (Fin n) (Fin n) (ZMod 2))) = 2 * r}
      =
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      rank A = 2 * r} := by
  let Coeff : Type := (i : Fin n) → ({j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
  let build : Coeff → Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun Q =>
      ((fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
        else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
        else 0) : Matrix (Fin n) (Fin n) (ZMod 2))
  have hshape :
      ∀ Q : Coeff,
        (∀ i : Fin n, build Q i i = 0) ∧
        (∀ i j : Fin n, build Q i j = build Q j i) := by
    intro Q
    have h := (upperTriangularCoeff_matrix_shape_and_injective n).1 Q
    simpa [build, Coeff] using h
  have hinj : Function.Injective build := by
    simpa [build, Coeff] using (upperTriangularCoeff_matrix_shape_and_injective n).2
  have rebuild_extract :
      ∀ A : {A : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, A i i = 0) ∧
          (∀ i j : Fin n, A i j = A j i) ∧
          rank A = 2 * r},
        build (fun i j => A.1 i j.1) = A.1 := by
    intro A
    ext i j
    dsimp [build]
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hij | hij_eq_nat | hji
    · rw [if_pos hij]
    · have hij_eq : i = j := Fin.ext hij_eq_nat
      subst j
      rw [if_neg (Nat.lt_irrefl (i : ℕ))]
      rw [if_neg (Nat.lt_irrefl (i : ℕ))]
      exact (A.2.1 i).symm
    · have hnot : ¬ (i : ℕ) < (j : ℕ) := Nat.not_lt.mpr (Nat.le_of_lt hji)
      rw [if_neg hnot]
      rw [if_pos hji]
      exact A.2.2.1 j i
  let e :
      {Q : Coeff // rank (build Q) = 2 * r} ≃
      {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * r} :=
    { toFun := fun Q =>
        ⟨build Q.1,
          by
            have hs := hshape Q.1
            exact ⟨hs.1, hs.2, Q.2⟩⟩
      invFun := fun A =>
        ⟨fun i j => A.1 i j.1,
          by
            have hmat := rebuild_extract A
            rw [hmat]
            exact A.2.2.2⟩
      left_inv := by
        intro Q
        apply Subtype.ext
        apply hinj
        exact rebuild_extract
          ⟨build Q.1,
            by
              have hs := hshape Q.1
              exact ⟨hs.1, hs.2, Q.2⟩⟩
      right_inv := by
        intro A
        apply Subtype.ext
        exact rebuild_extract A }
  exact Fintype.card_congr e










theorem upperTriangularRankFiber_canonicalContribution_count
    (n r : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ) :
    Fintype.card
      ({Q : ((i : Fin n) → ({j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)) //
        rank (((fun i j : Fin n =>
          if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
          else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
          else 0) : Matrix (Fin n) (Fin n) (ZMod 2))) = 2 * r} ×
      {p : (Fin r → ZMod 2) × (Fin r → ZMod 2) ×
          (Fin (n - 2 * r) → ZMod 2) × ZMod 2 //
        (∑ x : (Fin r → ZMod 2 × ZMod 2) ×
            (Fin (n - 2 * r) → ZMod 2),
          (if (Finset.univ.sum (fun i : Fin r =>
                (x.1 i).1 * (x.1 i).2 +
                  p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
              + Finset.univ.sum
                  (fun j : Fin (n - 2 * r) => p.2.2.1 j * x.2 j) = 0
           then (1 : ℤ) else (-1 : ℤ))) = 0}) =
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      rank A = 2 * r} *
      (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)) := by
  rw [Fintype.card_prod]
  rw [upperTriangularCoeff_rankFiber_card_eq_alternatingRankStratum n r rank]
  rw [canonicalRankBlock_balanced_affinePerturbation_count r (n - 2 * r)]












theorem upperTriangularRankStrata_canonicalContribution_sigma_count
    (n : ℕ)
    (rank : Matrix (Fin n) (Fin n) (ZMod 2) → ℕ) :
    Fintype.card
      (Σ r : Fin (n + 1),
        ({Q : ((i : Fin n) → ({j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)) //
          rank (((fun i j : Fin n =>
            if h : (i : ℕ) < (j : ℕ) then Q i ⟨j, h⟩
            else if h : (j : ℕ) < (i : ℕ) then Q j ⟨i, h⟩
            else 0) : Matrix (Fin n) (Fin n) (ZMod 2))) = 2 * (r : ℕ)} ×
        {p : (Fin (r : ℕ) → ZMod 2) × (Fin (r : ℕ) → ZMod 2) ×
            (Fin (n - 2 * (r : ℕ)) → ZMod 2) × ZMod 2 //
          (∑ x : (Fin (r : ℕ) → ZMod 2 × ZMod 2) ×
              (Fin (n - 2 * (r : ℕ)) → ZMod 2),
            (if (Finset.univ.sum (fun i : Fin (r : ℕ) =>
                  (x.1 i).1 * (x.1 i).2 +
                    p.1 i * (x.1 i).1 + p.2.1 i * (x.1 i).2) + p.2.2.2)
                + Finset.univ.sum
                    (fun j : Fin (n - 2 * (r : ℕ)) => p.2.2.1 j * x.2 j) = 0
             then (1 : ℤ) else (-1 : ℤ))) = 0})) =
    (∑ r : Fin (n + 1),
      Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        rank A = 2 * (r : ℕ)} *
        (2 ^ (2 * (r : ℕ) + 1) * (2 ^ (n - 2 * (r : ℕ)) - 1))) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  simpa using upperTriangularRankFiber_canonicalContribution_count n (r : ℕ) rank




theorem alternating_matrix_top_left_zero_diag_symmetric
    (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))
    (hdiag : ∀ i : Fin (n + 1), A i i = 0)
    (hsymm : ∀ i j : Fin (n + 1), A i j = A j i) :
    (∀ i : Fin n, A (Fin.castSucc i) (Fin.castSucc i) = 0) ∧
      (∀ i j : Fin n,
        A (Fin.castSucc i) (Fin.castSucc j) =
          A (Fin.castSucc j) (Fin.castSucc i)) := by
  exact And.intro
    (fun i => hdiag (Fin.castSucc i))
    (fun i j => hsymm (Fin.castSucc i) (Fin.castSucc j))




theorem alternating_matrix_border_matrix_spec
    (n : ℕ)
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2)
    (hBdiag : ∀ i : Fin n, B i i = 0)
    (hBsymm : ∀ i j : Fin n, B i j = B j i) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              v ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              v ⟨(j : ℕ), hj⟩
            else
              0;
      ((∀ i : Fin (n + 1), A i i = 0) ∧
          (∀ i j : Fin (n + 1), A i j = A j i)) ∧
        (∀ i j : Fin n, A (Fin.castSucc i) (Fin.castSucc j) = B i j) ∧
        (∀ i : Fin n, A (Fin.castSucc i) (Fin.last n) = v i) ∧
        (∀ i : Fin n, A (Fin.last n) (Fin.castSucc i) = v i) ∧
        A (Fin.last n) (Fin.last n) = 0) := by
  classical
    dsimp
    constructor
    · constructor
      · intro i
        by_cases hi : (i : ℕ) < n
        · simp [hi, hBdiag]
        · simp [hi]
      · intro i j
        by_cases hi : (i : ℕ) < n
        · by_cases hj : (j : ℕ) < n
          · simp [hi, hj, hBsymm]
          · simp [hi, hj]
        · by_cases hj : (j : ℕ) < n
          · simp [hi, hj]
          · simp [hi, hj]
    · constructor
      · intro i j
        simp
      · constructor
        · intro i
          simp
        · constructor
          · intro i
            simp
          · simp










theorem alternatingMatrix_succ_border_decomposition
    (n : ℕ) :
    Nonempty
      ({A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
          (∀ i : Fin (n + 1), A i i = 0) ∧
          (∀ i j : Fin (n + 1), A i j = A j i)} ≃
        ({B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i)} × (Fin n → ZMod 2))) := by
  classical
  let S : ℕ → Type := fun m =>
    {A : Matrix (Fin m) (Fin m) (ZMod 2) //
      (∀ i : Fin m, A i i = 0) ∧
      (∀ i j : Fin m, A i j = A j i)}
  let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  let toF : S (n + 1) → S n × (Fin n → ZMod 2) := fun A =>
    (⟨(fun i j => A.1 (Fin.castSucc i) (Fin.castSucc j)), by
        constructor
        · intro i
          exact A.2.1 (Fin.castSucc i)
        · intro i j
          exact A.2.2 (Fin.castSucc i) (Fin.castSucc j)⟩,
      fun i => A.1 (Fin.castSucc i) last)
  let fromF : S n × (Fin n → ZMod 2) → S (n + 1) := fun p =>
    ⟨(fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            p.2 ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            p.2 ⟨(j : ℕ), hj⟩
          else
            0), by
        constructor
        · intro i
          by_cases hi : (i : ℕ) < n
          · simp [hi, p.1.2.1 ⟨(i : ℕ), hi⟩]
          · simp [hi]
        · intro i j
          by_cases hi : (i : ℕ) < n
          · by_cases hj : (j : ℕ) < n
            · simp [hi, hj, p.1.2.2 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩]
            · simp [hi, hj]
          · by_cases hj : (j : ℕ) < n
            · simp [hi, hj]
            · simp [hi, hj]⟩
  exact ⟨{
    toFun := toF
    invFun := fromF
    left_inv := by
      intro A
      apply Subtype.ext
      funext i j
      dsimp [fromF, toF]
      by_cases hi : (i : ℕ) < n
      · by_cases hj : (j : ℕ) < n
        · simp [hi, hj]
        · have hjlast : j = last := by
            apply Fin.ext
            exact Nat.le_antisymm (Nat.lt_succ_iff.mp j.isLt) (Nat.le_of_not_gt hj)
          simp [hi, hjlast]
      · have hilast : i = last := by
          apply Fin.ext
          exact Nat.le_antisymm (Nat.lt_succ_iff.mp i.isLt) (Nat.le_of_not_gt hi)
        by_cases hj : (j : ℕ) < n
        · have hjcast : Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n) = j := by
            ext
            rfl
          have hsym : A.1 (Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n)) last = A.1 i j := by
            calc
              A.1 (Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n)) last =
                  A.1 last (Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n)) := A.2.2 _ _
              _ = A.1 i j := by simp [hilast, hjcast]
          simpa [hi, hj] using hsym
        · have hjlast : j = last := by
            apply Fin.ext
            exact Nat.le_antisymm (Nat.lt_succ_iff.mp j.isLt) (Nat.le_of_not_gt hj)
          simp [hilast, hjlast, A.2.1 last]
    right_inv := by
      intro p
      cases p with
      | mk B v =>
        apply Prod.ext
        · apply Subtype.ext
          funext i j
          dsimp [toF, fromF]
          simp
        · funext i
          dsimp [toF, fromF, last]
          simp
  }⟩






theorem symmetric_matrix_dot_double_sum_swap
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (u w : Fin n → ZMod 2) :
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : Fin n => w i * (B i j * u j))) =
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n => u i * (B i j * w j))) := by
  classical
    rw [Finset.sum_comm]
    simp [hsymm, mul_comm, mul_left_comm]


theorem symmetric_tolin_dot_comm
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (u w : Fin n → ZMod 2) :
    Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * w i) =
      Finset.univ.sum (fun i : Fin n => u i * (B.toLin' w) i) := by
  classical
    change (∑ i : Fin n, (∑ j : Fin n, B i j * u j) * w i) =
        ∑ i : Fin n, u i * (∑ j : Fin n, B i j * w j)
    calc
      (∑ i : Fin n, (∑ j : Fin n, B i j * u j) * w i)
          = ∑ i : Fin n, ∑ j : Fin n, w i * (B i j * u j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            ac_rfl
      _ = ∑ i : Fin n, ∑ j : Fin n, u i * (B i j * w j) := by
            exact symmetric_matrix_dot_double_sum_swap n B hsymm u w
      _ = ∑ i : Fin n, u i * (∑ j : Fin n, B i j * w j) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.mul_sum]




theorem borderblock_card_eq_zerofiber_of_notrangewitness
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v z : Fin n → ZMod 2)
    (hz : B.toLin' z = 0)
    (hdot : Finset.univ.sum (fun i : Fin n => v i * z i) = 1) :
    Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
      B.toLin' wt.1 + wt.2 • v = 0 ∧
        Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
      =
    Fintype.card {w : Fin n → ZMod 2 //
      B.toLin' w = 0 ∧
        Finset.univ.sum (fun i : Fin n => v i * w i) = 0} := by
  classical
  let A : Type := {wt : (Fin n → ZMod 2) × ZMod 2 //
    B.toLin' wt.1 + wt.2 • v = 0 ∧
      Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
  let C : Type := {w : Fin n → ZMod 2 //
    B.toLin' w = 0 ∧
      Finset.univ.sum (fun i : Fin n => v i * w i) = 0}
  change Fintype.card A = Fintype.card C
  have scalar_zero : ∀ wt : A, wt.1.2 = 0 := by
    intro wt
    have ht_cases : wt.1.2 = 0 ∨ wt.1.2 = 1 := by
      have h_all : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
        decide
      exact h_all wt.1.2
    cases ht_cases with
    | inl h0 => exact h0
    | inr h1 =>
        exfalso
        have hB : B.toLin' wt.1.1 = v := by
          funext i
          have hi : (B.toLin' wt.1.1 + wt.1.2 • v) i = (0 : Fin n → ZMod 2) i := by
            exact congrFun wt.2.1 i
          have hi' : (B.toLin' wt.1.1) i + v i = 0 := by
            simpa [Pi.add_apply, h1] using hi
          calc
            (B.toLin' wt.1.1) i = (B.toLin' wt.1.1) i + 0 := by simp
            _ = (B.toLin' wt.1.1) i + (v i + v i) := by
              rw [zmodTwo_add_self_eq_zero]
            _ = ((B.toLin' wt.1.1) i + v i) + v i := by ring
            _ = 0 + v i := by rw [hi']
            _ = v i := by simp
        have hdot0 : Finset.univ.sum (fun i : Fin n => v i * z i) = 0 := by
          calc
            Finset.univ.sum (fun i : Fin n => v i * z i)
                = Finset.univ.sum (fun i : Fin n => (B.toLin' wt.1.1) i * z i) := by
                  simp [hB]
            _ = Finset.univ.sum (fun i : Fin n => wt.1.1 i * (B.toLin' z) i) := by
                  exact symmetric_tolin_dot_comm n B hsymm wt.1.1 z
            _ = Finset.univ.sum (fun i : Fin n => wt.1.1 i * (0 : Fin n → ZMod 2) i) := by
                  rw [hz]
            _ = 0 := by simp
        have h10 : (1 : ZMod 2) = 0 := by
          calc
            (1 : ZMod 2) = Finset.univ.sum (fun i : Fin n => v i * z i) := by
              exact hdot.symm
            _ = 0 := hdot0
        exact one_ne_zero h10
  exact Fintype.card_congr
    { toFun := fun wt : A =>
        ⟨wt.1.1, by
          constructor
          · have ht : wt.1.2 = 0 := scalar_zero wt
            have hB : B.toLin' wt.1.1 + wt.1.2 • v = 0 := wt.2.1
            rw [ht] at hB
            simpa using hB
          · exact wt.2.2⟩
      invFun := fun w : C =>
        ⟨(w.1, 0), by
          constructor
          · simp [w.2.1]
          · exact w.2.2⟩
      left_inv := fun wt => by
        apply Subtype.ext
        exact Prod.ext rfl (scalar_zero wt).symm
      right_inv := fun w => by
        apply Subtype.ext
        rfl }




theorem kernel_dot_zerofiber_double_card_of_witness
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v z : Fin n → ZMod 2)
    (hz : B.toLin' z = 0)
    (hdot : Finset.univ.sum (fun i : Fin n => v i * z i) = 1) :
    2 * Fintype.card {w : Fin n → ZMod 2 //
      B.toLin' w = 0 ∧
        Finset.univ.sum (fun i : Fin n => v i * w i) = 0}
      =
    Fintype.card {w : Fin n → ZMod 2 // B.toLin' w = 0} := by
  classical
  let α := Fin n → ZMod 2
  let L : α → ZMod 2 := fun w => Finset.univ.sum (fun i : Fin n => v i * w i)
  let K := {w : α // B.toLin' w = 0}
  let K0 := {w : α // B.toLin' w = 0 ∧ L w = 0}
  let K1 := {w : α // B.toLin' w = 0 ∧ L w = 1}
  have hLz : L z = 1 := by
    change Finset.univ.sum (fun i : Fin n => v i * z i) = 1
    exact hdot
  have hL_add : ∀ w : α, L (w + z) = L w + L z := by
    intro w
    dsimp [L]
    calc
      Finset.univ.sum (fun i : Fin n => v i * (w + z) i)
          = Finset.univ.sum (fun i : Fin n => v i * w i + v i * z i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Pi.add_apply, mul_add]
      _ = Finset.univ.sum (fun i : Fin n => v i * w i)
            + Finset.univ.sum (fun i : Fin n => v i * z i) := by
            rw [Finset.sum_add_distrib]
  have hZ : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
    intro a
    fin_cases a
    · left
      rfl
    · right
      rfl
  have htrans0 : K0 ≃ K1 :=
    { toFun := fun x =>
        ⟨x.1 + z, by
          constructor
          · calc
              B.toLin' (x.1 + z) = B.toLin' x.1 + B.toLin' z := B.toLin'.map_add x.1 z
              _ = 0 + 0 := by rw [x.2.1, hz]
              _ = 0 := by rw [zero_add]
          · calc
              L (x.1 + z) = L x.1 + L z := hL_add x.1
              _ = 0 + 1 := by rw [x.2.2, hLz]
              _ = 1 := by rw [zero_add]
        ⟩
      invFun := fun x =>
        ⟨x.1 + z, by
          constructor
          · calc
              B.toLin' (x.1 + z) = B.toLin' x.1 + B.toLin' z := B.toLin'.map_add x.1 z
              _ = 0 + 0 := by rw [x.2.1, hz]
              _ = 0 := by rw [zero_add]
          · calc
              L (x.1 + z) = L x.1 + L z := hL_add x.1
              _ = 1 + 1 := by rw [x.2.2, hLz]
              _ = 0 := zmodTwo_add_self_eq_zero (1 : ZMod 2)
        ⟩
      left_inv := fun x => by
        ext i
        change x.1 i + z i + z i = x.1 i
        calc
          x.1 i + z i + z i = x.1 i + (z i + z i) := by rw [add_assoc]
          _ = x.1 i + 0 := by rw [zmodTwo_add_self_eq_zero (z i)]
          _ = x.1 i := by rw [add_zero]
      right_inv := fun x => by
        ext i
        change x.1 i + z i + z i = x.1 i
        calc
          x.1 i + z i + z i = x.1 i + (z i + z i) := by rw [add_assoc]
          _ = x.1 i + 0 := by rw [zmodTwo_add_self_eq_zero (z i)]
          _ = x.1 i := by rw [add_zero] }
  have hcard01 : Fintype.card K0 = Fintype.card K1 := Fintype.card_congr htrans0
  have hsplitEquiv : K ≃ Sum K0 K1 :=
    { toFun := fun x =>
        if hx0 : L x.1 = 0 then
          Sum.inl ⟨x.1, ⟨x.2, hx0⟩⟩
        else
          Sum.inr ⟨x.1, ⟨x.2, by
            cases hZ (L x.1) with
            | inl h0 => exact False.elim (hx0 h0)
            | inr h1 => exact h1⟩⟩
      invFun := fun x =>
        match x with
        | Sum.inl y => ⟨y.1, y.2.1⟩
        | Sum.inr y => ⟨y.1, y.2.1⟩
      left_inv := fun x => by
        dsimp
        by_cases hx0 : L x.1 = 0
        · rw [dif_pos hx0]
          rfl
        · rw [dif_neg hx0]
          rfl
      right_inv := fun x => by
        cases x with
        | inl y =>
            dsimp
            rw [dif_pos y.2.2]
            apply congrArg Sum.inl
            ext i
            rfl
        | inr y =>
            dsimp
            have hy0 : ¬ (L y.1 = 0) := by
              intro hy
              have h10 : (1 : ZMod 2) = 0 := by
                rw [← y.2.2]
                exact hy
              exact one_ne_zero h10
            rw [dif_neg hy0]
            apply congrArg Sum.inr
            ext i
            rfl }
  have hcardsplit : Fintype.card K = Fintype.card K0 + Fintype.card K1 := by
    calc
      Fintype.card K = Fintype.card (Sum K0 K1) := Fintype.card_congr hsplitEquiv
      _ = Fintype.card K0 + Fintype.card K1 := Fintype.card_sum
  change 2 * Fintype.card K0 = Fintype.card K
  calc
    2 * Fintype.card K0 = Fintype.card K0 + Fintype.card K0 := by omega
    _ = Fintype.card K0 + Fintype.card K1 := by rw [hcard01]
    _ = Fintype.card K := by rw [← hcardsplit]








theorem borderBlock_kernel_card_eq_of_notRangeWitness
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (_hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v z : Fin n → ZMod 2)
    (hz : B.toLin' z = 0)
    (hdot : Finset.univ.sum (fun i : Fin n => v i * z i) = 1) :
    2 * Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
      B.toLin' wt.1 + wt.2 • v = 0 ∧
        Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
      = Fintype.card {w : Fin n → ZMod 2 // B.toLin' w = 0} := by
  classical
  rw [borderblock_card_eq_zerofiber_of_notrangewitness n B hsymm v z hz hdot]
  exact kernel_dot_zerofiber_double_card_of_witness n B v z hz hdot






theorem zero_diag_symmetric_double_sum_eq_zero
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (w : Fin n → ZMod 2) :
    Finset.univ.sum
        (fun p : Fin n × Fin n => w p.1 * B p.1 p.2 * w p.2) = 0 := by
  classical
    let q : Fin n → Fin n → ZMod 2 := fun i j => w i * B i j * w j
    have hdiagq : ∀ i : Fin n, q i i = 0 := by
      intro i
      dsimp [q]
      rw [hdiag i]
      simp
    have hsymmq : ∀ i j : Fin n, q i j = q j i := by
      intro i j
      dsimp [q]
      rw [hsymm i j]
      ring
    have hsum_subset :
        ∀ s : Finset (Fin n), s.sum (fun i => s.sum (fun j => q i j)) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simp
      | insert a s ha ih =>
          have hcross :
              s.sum (fun i => q i a) = s.sum (fun i => q a i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hsymmq i a
          simp_rw [Finset.sum_insert ha]
          rw [hdiagq a]
          simp only [zero_add, Finset.sum_add_distrib, ih, add_zero]
          rw [hcross]
          ring_nf
          have htwo : (2 : ZMod 2) = 0 := by
            decide
          rw [htwo, mul_zero]
    change (Finset.univ.sum (fun p : Fin n × Fin n => q p.1 p.2)) = 0
    rw [Fintype.sum_prod_type]
    simpa using hsum_subset (Finset.univ : Finset (Fin n))


theorem zero_diag_symmetric_self_dot_tolin_eq_zero
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (w : Fin n → ZMod 2) :
    Finset.univ.sum (fun i : Fin n => w i * (B.toLin' w) i) = 0 := by
  classical
    rw [show Finset.univ.sum (fun i : Fin n => w i * (B.toLin' w) i) =
        Finset.univ.sum (fun p : Fin n × Fin n => w p.1 * B p.1 p.2 * w p.2) by
      rw [Fintype.sum_prod_type]
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]
    exact zero_diag_symmetric_double_sum_eq_zero n B hdiag hsymm w




theorem borderblock_zero_fiber_card_eq_kernel
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (u : Fin n → ZMod 2) :
    Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
      (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
        (Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i)) = 0) ∧
        wt.2 = 0}
      = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
  classical
  have _ := hdiag
  exact Fintype.card_congr
    { toFun := fun wt => ⟨wt.1.1, by
        have hlin := wt.2.1.1
        have hborder := wt.2.2
        simp [hborder] at hlin
        exact hlin⟩
      invFun := fun z => ⟨(z.1, 0), by
        constructor
        · constructor
          · simp [z.2]
          · have hcomm := symmetric_tolin_dot_comm n B hsymm u z.1
            calc
              (Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * z.1 i))
                  = Finset.univ.sum (fun i : Fin n => u i * (B.toLin' z.1) i) := hcomm
              _ = 0 := by simp [z.2]
        · rfl⟩
      left_inv := by
        intro wt
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact wt.2.2.symm
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }




theorem borderblock_one_fiber_card_eq_kernel
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (u : Fin n → ZMod 2) :
    Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
      (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
        (Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i)) = 0) ∧
        wt.2 = 1}
      = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
  classical
    have htwo : ∀ a : ZMod 2, a + a = 0 := by
      intro a
      calc
        a + a = (2 : ZMod 2) * a := by ring
        _ = 0 := by
          have hchar : (2 : ZMod 2) = 0 := by
            exact CharP.cast_eq_zero (ZMod 2) 2
          simp [hchar]
    apply Fintype.card_congr
    exact
      { toFun := fun wt =>
          ⟨wt.1.1 + u, by
            have hlin : B.toLin' wt.1.1 + wt.1.2 • B.toLin' u = 0 := wt.2.1.1
            simpa [wt.2.2, LinearMap.map_add] using hlin⟩
        invFun := fun z =>
          ⟨(z.1 + u, 1), by
            constructor
            · constructor
              · have hz : B.toLin' z.1 = 0 := z.2
                ext i
                simp [LinearMap.map_add, hz, htwo]
              · have hzDot :
                    (Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * z.1 i)) = 0 := by
                  have hcomm := symmetric_tolin_dot_comm n B hsymm u z.1
                  simpa [z.2] using hcomm
                have huDot :
                    (Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * u i)) = 0 := by
                  have hself := zero_diag_symmetric_self_dot_tolin_eq_zero n B hdiag hsymm u
                  simpa [mul_comm] using hself
                change (Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * ((z.1 + u) i))) = 0
                calc
                  (Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * ((z.1 + u) i)))
                      = Finset.univ.sum
                          (fun i : Fin n => (B.toLin' u) i * z.1 i + (B.toLin' u) i * u i) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        simp [mul_add]
                  _ = Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * z.1 i) +
                        Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * u i) := by
                        rw [Finset.sum_add_distrib]
                  _ = 0 := by
                        rw [hzDot, huDot, zero_add]
            · rfl⟩
        left_inv := by
          intro wt
          apply Subtype.ext
          apply Prod.ext
          · ext i
            calc
              ((wt.1.1 i + u i) + u i) = wt.1.1 i + (u i + u i) := by rw [add_assoc]
              _ = wt.1.1 i + 0 := by rw [htwo (u i)]
              _ = wt.1.1 i := by rw [add_zero]
          · exact wt.2.2.symm
        right_inv := by
          intro z
          apply Subtype.ext
          ext i
          calc
            ((z.1 i + u i) + u i) = z.1 i + (u i + u i) := by rw [add_assoc]
            _ = z.1 i + 0 := by rw [htwo (u i)]
            _ = z.1 i := by rw [add_zero] }








theorem borderBlock_kernel_card_eq_of_rangeVector
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (u : Fin n → ZMod 2) :
    Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
      B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
        Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0}
      = 2 * Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
  classical
  have zmod2_eq_zero_or_one : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by
    intro b
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  let e :
      {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
          Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0} ≃
        ({wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 0} ⊕
         {wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 1}) :=
    { toFun := fun wt =>
        if h : wt.1.2 = 0 then
          Sum.inl ⟨wt.1, wt.2, h⟩
        else
          Sum.inr ⟨wt.1, wt.2, by
            exact (zmod2_eq_zero_or_one wt.1.2).resolve_left h⟩,
      invFun := fun x =>
        match x with
        | Sum.inl wt => ⟨wt.1, wt.2.1⟩
        | Sum.inr wt => ⟨wt.1, wt.2.1⟩,
      left_inv := by
        intro wt
        by_cases h : wt.1.2 = 0
        · simp [h]
        · simp [h]
      right_inv := by
        intro x
        cases x with
        | inl wt =>
            simp [wt.2.2]
        | inr wt =>
            have hne : ¬ wt.1.2 = 0 := by
              intro h0
              exact (zero_ne_one : (0 : ZMod 2) ≠ 1) (h0.symm.trans wt.2.2)
            simp [hne] }
  have hsplit :
      Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
          Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0}
      = Fintype.card ({wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 0} ⊕
         {wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 1}) :=
    Fintype.card_congr e
  have hz := borderblock_zero_fiber_card_eq_kernel n B hdiag hsymm u
  have ho := borderblock_one_fiber_card_eq_kernel n B hdiag hsymm u
  calc
    Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
          Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0}
        = Fintype.card ({wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 0} ⊕
         {wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 1}) := hsplit
    _ = Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 0} +
        Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
          (B.toLin' wt.1 + wt.2 • B.toLin' u = 0 ∧
            Finset.univ.sum (fun i : Fin n => (B.toLin' u) i * wt.1 i) = 0) ∧
            wt.2 = 1} := by
          simp
    _ = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} +
        Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
          rw [hz, ho]
    _ = 2 * Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
          omega




theorem exists_kernel_vector_represents_dual
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (g : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hg : ∀ x : Fin n → ZMod 2, g (B.toLin' x) = 0) :
    ∃ z : Fin n → ZMod 2,
      B.toLin' z = 0 ∧
        ∀ x : Fin n → ZMod 2,
          g x = Finset.univ.sum (fun i : Fin n => x i * z i) := by
  classical
  let z : Fin n → ZMod 2 := fun i => g (Pi.single i 1)
  have decompose : ∀ x : Fin n → ZMod 2,
      x = Finset.univ.sum (fun i : Fin n =>
        x i • (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) := by
    intro x
    funext k
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      have hsingle_zero :
          ((Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) k) = 0 := by
        rw [Pi.single_eq_of_ne]
        exact hbk.symm
      simp [hsingle_zero]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  have repr : ∀ x : Fin n → ZMod 2,
      g x = Finset.univ.sum (fun i : Fin n => x i * z i) := by
    intro x
    calc
      g x = g (Finset.univ.sum (fun i : Fin n =>
          x i • (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))) := by
        rw [← decompose x]
      _ = Finset.univ.sum (fun i : Fin n =>
          g (x i • (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))) := by
        rw [map_sum]
      _ = Finset.univ.sum (fun i : Fin n => x i * z i) := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          simp [z]
  use z
  constructor
  · funext j
    have hzero :
        Finset.univ.sum (fun i : Fin n =>
          (B.toLin' (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)) i * z i) = 0 := by
      rw [← repr (B.toLin' (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2))]
      exact hg (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)
    have hcomm :=
      symmetric_tolin_dot_comm n B hsymm
        (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) z
    rw [hcomm] at hzero
    have hdot :
        Finset.univ.sum (fun i : Fin n =>
          (B.toLin' z) i * ((Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i)) = 0 := by
      simpa [mul_comm] using hzero
    have hsingle :
        Finset.univ.sum (fun i : Fin n =>
          (B.toLin' z) i * ((Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i)) =
            (B.toLin' z) j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b hb hbj
        have hsingle_zero :
            ((Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) b) = 0 := by
          rw [Pi.single_eq_of_ne]
          exact hbj
        simp [hsingle_zero]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    rw [hsingle] at hdot
    exact hdot
  · exact repr




theorem matrix_tolin_dot_sum_expand
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (a b : Fin n → ZMod 2) :
    Finset.univ.sum (fun i : Fin n => a i * (B.toLin' b) i) =
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n => a i * (B i j * b j))) := by
  classical
  simp only [Matrix.toLin'_apply, Matrix.mulVec]
  unfold dotProduct
  simp only [Finset.mul_sum]


theorem finite_coord_submodule_exists_annihilator_of_not_mem
    (n : ℕ) (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : v ∉ W) :
    ∃ g : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (∀ w : Fin n → ZMod 2, w ∈ W → g w = 0) ∧ g v = 1 := by
  classical
    have exists_dual :
        ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Module.Free (ZMod 2) M],
          ∀ x : M, x ≠ 0 → ∃ φ : M →ₗ[ZMod 2] ZMod 2, φ x = 1 := by
      intro M _ _ _ x hx
      let b := Module.Free.chooseBasis (ZMod 2) M
      have hxrepr : b.repr x ≠ 0 := by
        intro h
        apply hx
        exact b.repr.injective (by simpa using h)
      have h_exists : ∃ i, b.repr x i ≠ 0 := by
        by_contra h
        apply hxrepr
        ext i
        by_contra hi
        exact h ⟨i, hi⟩
      rcases h_exists with ⟨i, hi⟩
      let coord : M →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun y => b.repr y i
          map_add' := by
            intro y z
            simp
          map_smul' := by
            intro a y
            simp }
      use (b.repr x i)⁻¹ • coord
      dsimp [coord]
      exact inv_mul_cancel₀ hi
    have hq : W.mkQ v ≠ 0 := by
      intro h
      exact hv (by simpa using h)
    obtain ⟨φ, hφ⟩ := exists_dual (M := (Fin n → ZMod 2) ⧸ W) (W.mkQ v) hq
    use φ.comp W.mkQ
    constructor
    · intro w hw
      have hwq : W.mkQ w = 0 := by
        simpa using hw
      simp [hwq]
    · simpa using hφ




theorem linear_functional_coord_sum_zmod2
    (n : ℕ) (g : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : Fin n → ZMod 2) :
    g x = (Finset.univ.sum fun i : Fin n => x i * g (Pi.single i 1)) := by
  classical
  have hx : x = Finset.univ.sum fun i : Fin n => Pi.single i (x i) := by
    ext j
    simp
  calc
    g x = g (Finset.univ.sum fun i : Fin n => Pi.single i (x i)) := by
      exact congrArg g hx
    _ = Finset.univ.sum fun i : Fin n => g (Pi.single i (x i)) := by
      exact map_sum g (fun i : Fin n => Pi.single i (x i)) Finset.univ
    _ = Finset.univ.sum fun i : Fin n =>
        x i * g ((Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsingle :
          Pi.single i (x i) =
            x i • (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) := by
        ext j
        by_cases h : j = i
        · subst j
          simp
        · simp [Pi.single_eq_of_ne h]
      rw [hsingle, LinearMap.map_smul]
      rfl




theorem symmetric_matrix_column_in_range
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (_hsymm : ∀ i j : Fin n, B i j = B j i) (j : Fin n) :
    (fun i : Fin n => B i j) ∈ LinearMap.range B.toLin' := by
  classical
    exact ⟨Pi.single j 1, by
      ext i
      simp [Matrix.mulVec]⟩


theorem exists_tolin_kernel_dot_one_of_not_mem_range
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2)
    (hv : v ∉ LinearMap.range (B.toLin')) :
    ∃ z : Fin n → ZMod 2,
      B.toLin' z = 0 ∧
        Finset.univ.sum (fun i : Fin n => v i * z i) = 1 := by
  classical
    obtain ⟨g, hg_range, hgv⟩ :=
      finite_coord_submodule_exists_annihilator_of_not_mem n (LinearMap.range B.toLin') v hv
    let z : Fin n → ZMod 2 := fun i => g (Pi.single i 1)
    use z
    constructor
    · ext j
      have hrow_range : (fun i : Fin n => B j i) ∈ LinearMap.range B.toLin' := by
        have hrow_eq_col : (fun i : Fin n => B j i) = (fun i : Fin n => B i j) := by
          funext i
          exact hsymm j i
        rw [hrow_eq_col]
        exact symmetric_matrix_column_in_range n B hsymm j
      have hgzrow : g (fun i : Fin n => B j i) = 0 :=
        hg_range (fun i : Fin n => B j i) hrow_range
      have hrep_row :
          g (fun i : Fin n => B j i) =
            (Finset.univ.sum fun i : Fin n => B j i * z i) := by
        simpa [z] using linear_functional_coord_sum_zmod2 n g (fun i : Fin n => B j i)
      have hsum : (Finset.univ.sum fun i : Fin n => B j i * z i) = 0 := by
        calc
          (Finset.univ.sum fun i : Fin n => B j i * z i) = g (fun i : Fin n => B j i) := hrep_row.symm
          _ = 0 := hgzrow
      change (Finset.univ.sum fun i : Fin n => B j i * z i) = 0
      exact hsum
    · have hrep_v :
          g v = (Finset.univ.sum fun i : Fin n => v i * z i) := by
        simpa [z] using linear_functional_coord_sum_zmod2 n g v
      calc
        (Finset.univ.sum fun i : Fin n => v i * z i) = g v := hrep_v.symm
        _ = 1 := hgv







theorem upperTriangular_walsh_support_difference_mem_range_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a b : Fin n -> ZMod 2)
    (ha :
      (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => a i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0)
    (hb :
      (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => b i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0) :
    (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      (fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0);
     a + b ∈ LinearMap.range (Matrix.toLin' A)) := by
  classical
    let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0
    change a + b ∈ LinearMap.range (Matrix.toLin' A)
    have haPhase :=
      (upperTriangular_walsh_nonzero_iff_vanishes_on_kernel_q2 n Q a).mp ha
    have hbPhase :=
      (upperTriangular_walsh_nonzero_iff_vanishes_on_kernel_q2 n Q b).mp hb
    have hsymm : ∀ i j : Fin n, A i j = A j i := by
      intro i j
      simpa [A] using (upper_triangular_quadratic_coeff_to_alt_matrix_valid_q2 n Q).2 i j
    by_contra hnot
    rcases exists_tolin_kernel_dot_one_of_not_mem_range n A hsymm (a + b) hnot with
      ⟨z, hz, hdot⟩
    let qz : ZMod 2 :=
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * z i * z j.1))
    let az : ZMod 2 := Finset.univ.sum (fun i : Fin n => a i * z i)
    let bz : ZMod 2 := Finset.univ.sum (fun i : Fin n => b i * z i)
    have ha_z : qz + az = 0 := by
      simpa [qz, az, A] using haPhase z (by simpa [A] using hz)
    have hb_z : qz + bz = 0 := by
      simpa [qz, bz, A] using hbPhase z (by simpa [A] using hz)
    have hsum : Finset.univ.sum (fun i : Fin n => (a + b) i * z i) = 0 := by
      have hdot_add :
          Finset.univ.sum (fun i : Fin n => (a + b) i * z i) = az + bz := by
        simp [az, bz, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      have hphase_add : (qz + az) + (qz + bz) = 0 := by
        rw [ha_z, hb_z]
        simp
      have hdot_zero : az + bz = 0 := by
        calc
          az + bz = (qz + qz) + (az + bz) := by
            simp [zmodTwo_add_self_eq_zero qz]
          _ = (qz + az) + (qz + bz) := by
            abel
          _ = 0 := hphase_add
      rw [hdot_add, hdot_zero]
    have hcontr : (0 : ZMod 2) = 1 := by
      rw [← hsum]
      exact hdot
    exact (zero_ne_one : (0 : ZMod 2) ≠ 1) hcontr
























theorem upper_triangular_phase_add_linear_split_q2
    (n : Nat)
    (Q : (i : Fin n) → {j : Fin n // (i : Nat) < (j : Nat)} → ZMod 2)
    (a c y : Fin n → ZMod 2) :
    (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1)) +
      Finset.univ.sum (fun i : Fin n => (a i + c i) * y i)) =
    (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1)) +
      Finset.univ.sum (fun i : Fin n => a i * y i)) +
    Finset.univ.sum (fun i : Fin n => c i * y i) := by
  classical
    simp only [add_mul, Finset.sum_add_distrib]
    ac_rfl






theorem symmetric_tolin_range_kernel_dot_zero_q2
    (n : Nat) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (c y : Fin n → ZMod 2)
    (hc : c ∈ LinearMap.range (Matrix.toLin' B))
    (hy : (Matrix.toLin' B) y = 0) :
    Finset.univ.sum (fun i : Fin n => c i * y i) = 0 := by
  classical
  obtain ⟨x, hx⟩ := hc
  calc
    Finset.univ.sum (fun i : Fin n => c i * y i)
        = Finset.univ.sum (fun i : Fin n => ((Matrix.toLin' B) x) i * y i) := by
          simp [hx]
    _ = Finset.univ.sum (fun i : Fin n => x i * ((Matrix.toLin' B) y) i) :=
          symmetric_tolin_dot_comm n B hsymm x y
    _ = 0 := by
          simp [hy]


theorem upperTriangular_kernelVanishes_add_range_element_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a c : Fin n -> ZMod 2)
    (hker :
      (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
        (fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0);
       let phase : (Fin n -> ZMod 2) -> ZMod 2 := fun x =>
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n => a i * x i);
       forall y : Fin n -> ZMod 2,
        (Matrix.toLin' A) y = 0 -> phase y = 0))
    (hc :
      (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
        (fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0);
       c ∈ LinearMap.range (Matrix.toLin' A))) :
    (let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      (fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0);
     let phase : (Fin n -> ZMod 2) -> ZMod 2 := fun x =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * x i * x j.1)) +
      Finset.univ.sum (fun i : Fin n => (a i + c i) * x i);
     forall y : Fin n -> ZMod 2,
      (Matrix.toLin' A) y = 0 -> phase y = 0) := by
  classical
  let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun i j : Fin n =>
      if h : (i : Nat) < (j : Nat) then
        Q i (Subtype.mk j h)
      else if h' : (j : Nat) < (i : Nat) then
        Q j (Subtype.mk i h')
      else
        0
  let quad : (Fin n -> ZMod 2) -> ZMod 2 := fun x =>
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
        Q i j * x i * x j.1))
  have hkerA : ∀ y : Fin n -> ZMod 2,
      (Matrix.toLin' A) y = 0 -> quad y + Finset.univ.sum (fun i : Fin n => a i * y i) = 0 := by
    simpa [A, quad] using hker
  have hcA : c ∈ LinearMap.range (Matrix.toLin' A) := by
    simpa [A] using hc
  have hsymm : ∀ i j : Fin n, A i j = A j i := by
    have h := upper_triangular_quadratic_coeff_to_alt_matrix_valid_q2 n Q
    simpa [A] using h.2
  change ∀ y : Fin n -> ZMod 2,
      (Matrix.toLin' A) y = 0 ->
        quad y + Finset.univ.sum (fun i : Fin n => (a i + c i) * y i) = 0
  intro y hy
  have hdot : Finset.univ.sum (fun i : Fin n => c i * y i) = 0 := by
    exact symmetric_tolin_range_kernel_dot_zero_q2 n A hsymm c y hcA hy
  have hOld : quad y + Finset.univ.sum (fun i : Fin n => a i * y i) = 0 := hkerA y hy
  calc
    quad y + Finset.univ.sum (fun i : Fin n => (a i + c i) * y i)
        = (quad y + Finset.univ.sum (fun i : Fin n => a i * y i)) +
            Finset.univ.sum (fun i : Fin n => c i * y i) := by
          simpa [quad] using upper_triangular_phase_add_linear_split_q2 n Q a c y
    _ = 0 := by
      simp [hOld, hdot]


theorem upperTriangular_walsh_nonzero_add_range_element_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a u : Fin n -> ZMod 2)
    (hu :
      u ∈ LinearMap.range
        (Matrix.toLin'
          ((fun i j : Fin n =>
            if h : (i : Nat) < (j : Nat) then
              Q i (Subtype.mk j h)
            else if h' : (j : Nat) < (i : Nat) then
              Q j (Subtype.mk i h')
            else
              0) : Matrix (Fin n) (Fin n) (ZMod 2))))
    (hW :
      Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * x i * x j.1))) +
          Finset.univ.sum (fun i : Fin n => a i * x i) = 0
        then
          (1 : Int)
        else
          (-1 : Int)) ≠ 0) :
    Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
      if
        (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * x i * x j.1))) +
        Finset.univ.sum (fun i : Fin n => (a + u) i * x i) = 0
      then
        (1 : Int)
      else
        (-1 : Int)) ≠ 0 := by
  simpa using
      (upperTriangular_walsh_nonzero_iff_vanishes_on_kernel_q2 n Q (a + u)).2
        (upperTriangular_kernelVanishes_add_range_element_q2 n Q a u
          ((upperTriangular_walsh_nonzero_iff_vanishes_on_kernel_q2 n Q a).1 hW) hu)









theorem zmod_two_anchor_coset_left_inverse_q2
    {n : Nat} (a0 a : Fin n -> ZMod 2) :
    a0 + (a + a0) = a := by
  simp [add_comm]


theorem upperTriangular_walshSupport_iff_anchor_range_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a0 a : Fin n -> ZMod 2)
    (h0 :
      (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => a0 i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0) :
    ((Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => a i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0) ↔
      (a + a0) ∈ LinearMap.range
        (Matrix.toLin'
          ((fun i j : Fin n =>
            if h : (i : Nat) < (j : Nat) then
              Q i (Subtype.mk j h)
            else if h' : (j : Nat) < (i : Nat) then
              Q j (Subtype.mk i h')
            else
              0) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
  exact
      Iff.intro
        (fun ha =>
          upperTriangular_walsh_support_difference_mem_range_q2 n Q a a0 ha h0)
        (fun hdiff =>
          by
            have hnonzero :=
              upperTriangular_walsh_nonzero_add_range_element_q2 n Q a0 (a + a0) hdiff h0
            have hmask : a0 + (a + a0) = a :=
              zmod_two_anchor_coset_left_inverse_q2 a0 a
            rw [hmask] at hnonzero
            exact hnonzero)









theorem zmod_two_anchor_coset_right_inverse_q2
    {n : Nat} (a0 a : Fin n -> ZMod 2) :
    (a0 + a) + a0 = a := by
  simp [add_comm]


theorem upperTriangular_walshSupport_anchor_shift_iff_range_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a0 u : Fin n -> ZMod 2)
    (h0 :
      (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => a0 i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0) :
    ((Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => (a0 + u) i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0) ↔
      u ∈ LinearMap.range
        (Matrix.toLin'
          ((fun i j : Fin n =>
            if h : (i : Nat) < (j : Nat) then
              Q i (Subtype.mk j h)
            else if h' : (j : Nat) < (i : Nat) then
              Q j (Subtype.mk i h')
            else
              0) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
  simpa [zmod_two_anchor_coset_right_inverse_q2 (a0 := a0) (a := u)] using (upperTriangular_walshSupport_iff_anchor_range_q2 n Q a0 (a0 + u) h0)





























theorem uppertriangular_walshsupport_anchor_shift_range_card_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a0 : Fin n -> ZMod 2)
    (h0 :
      (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => a0 i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0) :
    Fintype.card
      {a : (Fin n -> ZMod 2) //
        (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
          if
            (Finset.univ.sum (fun i : Fin n =>
                Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                  Q i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => a i * x i) = 0)
          then
            (1 : Int)
          else
            (-1 : Int))) ≠ 0} =
      Fintype.card
        (LinearMap.range
          (Matrix.toLin'
            ((fun i j : Fin n =>
              if h : (i : Nat) < (j : Nat) then
                Q i (Subtype.mk j h)
              else if h' : (j : Nat) < (i : Nat) then
                Q j (Subtype.mk i h')
              else
                0) : Matrix (Fin n) (Fin n) (ZMod 2)))) := by
  classical
  exact
    Fintype.card_congr
      { toFun := fun a =>
          ⟨a.1 + a0,
            (upperTriangular_walshSupport_anchor_shift_iff_range_q2 n Q a0 (a.1 + a0) h0).1
              (by
                rw [zmod_two_anchor_coset_left_inverse_q2 a0 a.1]
                exact a.2)⟩
        invFun := fun u =>
          ⟨a0 + u.1,
            (upperTriangular_walshSupport_anchor_shift_iff_range_q2 n Q a0 u.1 h0).2 u.2⟩
        left_inv := fun a => by
          apply Subtype.ext
          exact zmod_two_anchor_coset_left_inverse_q2 a0 a.1
        right_inv := fun u => by
          apply Subtype.ext
          exact zmod_two_anchor_coset_right_inverse_q2 a0 u.1 }




theorem card_range_tolin_prime_eq_pow_finrank
    (n k : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = k) :
    Fintype.card (LinearMap.range (B.toLin')) = 2 ^ k := by
  classical
    rw [← hrank]
    simpa [ZMod.card] using
      (Module.card_fintype
        (R := ZMod 2)
        (M := LinearMap.range (B.toLin'))
        (b := Module.finBasis (ZMod 2) (LinearMap.range (B.toLin'))))


theorem upperTriangular_walshSupport_card_eq_pow_rank_of_anchor_shift_q2
    (n r : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (a0 : Fin n -> ZMod 2)
    (h0 :
      (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if
          (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => a0 i * x i) = 0)
        then
          (1 : Int)
        else
          (-1 : Int))) ≠ 0)
    (hrank :
      Module.finrank (ZMod 2)
        (LinearMap.range
          (Matrix.toLin'
            ((fun i j : Fin n =>
              if h : (i : Nat) < (j : Nat) then
                Q i (Subtype.mk j h)
              else if h' : (j : Nat) < (i : Nat) then
                Q j (Subtype.mk i h')
              else
                0) : Matrix (Fin n) (Fin n) (ZMod 2)))) = 2 * r) :
    Fintype.card
      {a : (Fin n -> ZMod 2) //
        (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
          if
            (Finset.univ.sum (fun i : Fin n =>
                Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                  Q i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => a i * x i) = 0)
          then
            (1 : Int)
          else
            (-1 : Int))) ≠ 0} =
      2 ^ (2 * r) := by
  classical
    let B : Matrix (Fin n) (Fin n) (ZMod 2) :=
      ((fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0) : Matrix (Fin n) (Fin n) (ZMod 2))
    have hsupport :
        Fintype.card
          {a : (Fin n -> ZMod 2) //
            (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
              if
                (Finset.univ.sum (fun i : Fin n =>
                    Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                      Q i j * x i * x j.1)) +
                  Finset.univ.sum (fun i : Fin n => a i * x i) = 0)
              then
                (1 : Int)
              else
                (-1 : Int))) ≠ 0} =
          Fintype.card (LinearMap.range (Matrix.toLin' B)) := by
      simpa [B] using uppertriangular_walshsupport_anchor_shift_range_card_q2 n Q a0 h0
    calc
      Fintype.card
          {a : (Fin n -> ZMod 2) //
            (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
              if
                (Finset.univ.sum (fun i : Fin n =>
                    Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                      Q i j * x i * x j.1)) +
                  Finset.univ.sum (fun i : Fin n => a i * x i) = 0)
              then
                (1 : Int)
              else
                (-1 : Int))) ≠ 0}
          = Fintype.card (LinearMap.range (Matrix.toLin' B)) := hsupport
      _ = 2 ^ (2 * r) := by
        exact card_range_tolin_prime_eq_pow_finrank n (2 * r) B (by simpa [B] using hrank)





























theorem upper_triangular_quadratic_add_expansion_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (x y : Fin n -> ZMod 2) :
    Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (x + y) i * (x + y) j.1)) =
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * x i * x j.1)) +
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1)) +
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (x i * y j.1 + y i * x j.1))) := by
  classical
    simp only [Pi.add_apply]
    calc
      Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * (x i + y i) * (x j.1 + y j.1))) =
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            (Q i j * x i * x j.1 + Q i j * y i * y j.1) +
              Q i j * (x i * y j.1 + y i * x j.1))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * x i * x j.1)) +
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * y i * y j.1)) +
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
            Q i j * (x i * y j.1 + y i * x j.1))) := by
        simp only [Finset.sum_add_distrib]


theorem upperTriangular_kernel_quadratic_add_on_kernel_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (y z : Fin n -> ZMod 2)
    (hz :
      (Matrix.toLin'
        ((fun i j : Fin n =>
          if h : (i : Nat) < (j : Nat) then
            Q i (Subtype.mk j h)
          else if h' : (j : Nat) < (i : Nat) then
            Q j (Subtype.mk i h')
          else
            0) : Matrix (Fin n) (Fin n) (ZMod 2))) z = 0) :
    Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * (y + z) i * (y + z) j.1)) =
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1)) +
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * z i * z j.1)) := by
  rw [upper_triangular_quadratic_add_expansion_q2 n Q y z,
      upper_triangular_polar_cross_vanishes_of_kernel_q2 n Q z hz y,
      add_zero]












theorem uppertriangular_kernel_quadratic_linear_on_kernel_q2
    (n : Nat)
    (Q : (i : Fin n) → {j : Fin n // (i : Nat) < (j : Nat)} → ZMod 2) :
    let M : Matrix (Fin n) (Fin n) (ZMod 2) :=
      ((fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0) : Matrix (Fin n) (Fin n) (ZMod 2));
    let q : (Fin n → ZMod 2) → ZMod 2 := fun y =>
      (Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y (j.1))));
    ∃ qK : (LinearMap.ker (Matrix.toLin' M)) →ₗ[ZMod 2] ZMod 2,
      ∀ y : LinearMap.ker (Matrix.toLin' M), qK y = q (y.1) := by
  classical
  let M : Matrix (Fin n) (Fin n) (ZMod 2) :=
    ((fun i j : Fin n =>
      if h : (i : Nat) < (j : Nat) then
        Q i (Subtype.mk j h)
      else if h' : (j : Nat) < (i : Nat) then
        Q j (Subtype.mk i h')
      else
        0) : Matrix (Fin n) (Fin n) (ZMod 2))
  let q : (Fin n → ZMod 2) → ZMod 2 := fun y =>
    (Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
        Q i j * y i * y (j.1))))
  change ∃ qK : (LinearMap.ker (Matrix.toLin' M)) →ₗ[ZMod 2] ZMod 2,
    ∀ y : LinearMap.ker (Matrix.toLin' M), qK y = q (y.1)
  let qK : (LinearMap.ker (Matrix.toLin' M)) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun y => q y.1
      map_add' := by
        intro x y
        change q (x.1 + y.1) = q x.1 + q y.1
        simpa [q, M] using
          (upperTriangular_kernel_quadratic_add_on_kernel_q2 n Q x.1 y.1 y.2)
      map_smul' := by
        intro c y
        fin_cases c
        · change q ((0 : ZMod 2) • y.1) = (0 : ZMod 2) • q y.1
          simp [q]
        · change q ((1 : ZMod 2) • y.1) = (1 : ZMod 2) • q y.1
          simp [q] }
  exact ⟨qK, by intro y; rfl⟩




theorem zmod2_fin_submodule_linear_functional_extend
    (n : Nat)
    (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (f : W →ₗ[ZMod 2] ZMod 2) :
    ∃ g : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      ∀ w : W, g (w.1) = f w := by
  classical
    obtain ⟨g, hg⟩ := LinearMap.exists_extend f
    use g
    intro w
    have hw := congrArg (fun h : W →ₗ[ZMod 2] ZMod 2 => h w) hg
    simpa using hw




theorem upperTriangular_exists_kernel_vanishing_linear_q2
    (n : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2) :
    ∃ a0 : Fin n -> ZMod 2,
      ∀ y : Fin n -> ZMod 2,
        (Matrix.toLin'
          ((fun i j : Fin n =>
            if h : (i : Nat) < (j : Nat) then
              Q i (Subtype.mk j h)
            else if h' : (j : Nat) < (i : Nat) then
              Q j (Subtype.mk i h')
            else
              0) : Matrix (Fin n) (Fin n) (ZMod 2))) y = 0 ->
        (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * y i * y j.1)) +
          Finset.univ.sum (fun i : Fin n => a0 i * y i)) = 0 := by
  classical
    let M : Matrix (Fin n) (Fin n) (ZMod 2) :=
      ((fun i j : Fin n =>
        if h : (i : Nat) < (j : Nat) then
          Q i (Subtype.mk j h)
        else if h' : (j : Nat) < (i : Nat) then
          Q j (Subtype.mk i h')
        else
          0) : Matrix (Fin n) (Fin n) (ZMod 2))
    let q : (Fin n -> ZMod 2) -> ZMod 2 := fun y =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * y i * y j.1))
    rcases (uppertriangular_kernel_quadratic_linear_on_kernel_q2 n Q) with ⟨qK, hqK⟩
    rcases (zmod2_fin_submodule_linear_functional_extend n (Matrix.toLin' M).ker qK) with ⟨g, hg⟩
    exact ⟨fun i : Fin n => g (Pi.single i (1 : ZMod 2)), by
      intro y hy
      have hyK : y ∈ (Matrix.toLin' M).ker := by
        simpa [M] using hy
      let w : (Matrix.toLin' M).ker := ⟨y, hyK⟩
      have hg_y : g y = qK w := by
        simpa [w] using hg w
      have hq_y : qK w = q y := by
        simpa [w, q] using hqK w
      have hgy : g y = q y := hg_y.trans hq_y
      have hcoord := linear_functional_coord_sum_zmod2 n g y
      have hlin :
          (Finset.univ.sum (fun i : Fin n => g (Pi.single i (1 : ZMod 2)) * y i)) = g y := by
        calc
          (Finset.univ.sum (fun i : Fin n => g (Pi.single i (1 : ZMod 2)) * y i))
              = Finset.univ.sum (fun i : Fin n => y i * g (Pi.single i (1 : ZMod 2))) := by
                exact Finset.sum_congr rfl (fun i hi =>
                  mul_comm (g (Pi.single i (1 : ZMod 2))) (y i))
          _ = g y := by
                exact hcoord.symm
      calc
        (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
              Q i j * y i * y j.1)) +
          Finset.univ.sum (fun i : Fin n => g (Pi.single i (1 : ZMod 2)) * y i))
            = q y + g y := by
              change q y + Finset.univ.sum (fun i : Fin n => g (Pi.single i (1 : ZMod 2)) * y i) = q y + g y
              rw [hlin]
        _ = q y + q y := by
              rw [hgy]
        _ = 0 := by
              exact zmodTwo_add_self_eq_zero (q y)
    ⟩


theorem upperTriangular_walshSupport_card_eq_pow_rank_unconditional_q2
    (n r : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (hrank :
      Module.finrank (ZMod 2)
        (LinearMap.range
          (Matrix.toLin'
            ((fun i j : Fin n =>
              if h : (i : Nat) < (j : Nat) then
                Q i (Subtype.mk j h)
              else if h' : (j : Nat) < (i : Nat) then
                Q j (Subtype.mk i h')
              else
                0) : Matrix (Fin n) (Fin n) (ZMod 2)))) = 2 * r) :
    (let q : (Fin n -> ZMod 2) -> ZMod 2 := fun x =>
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
          Q i j * x i * x (j.1)));
     let W : (Fin n -> ZMod 2) -> Int := fun a =>
      Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
        if q x + Finset.univ.sum (fun i : Fin n => a i * x i) = 0 then
          (1 : Int)
        else
          (-1 : Int));
     Fintype.card {a : Fin n -> ZMod 2 // W a ≠ 0} = 2 ^ (2 * r)) := by
  exact Exists.elim (upperTriangular_exists_kernel_vanishing_linear_q2 n Q) (fun a0 hker =>
      by
        have h0 :
            (Finset.univ.sum (fun x : (Fin n -> ZMod 2) =>
              if
                (Finset.univ.sum (fun i : Fin n =>
                    Finset.univ.sum (fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
                      Q i j * x i * x j.1)) +
                  Finset.univ.sum (fun i : Fin n => a0 i * x i) = 0)
              then
                (1 : Int)
              else
                (-1 : Int))) ≠ 0 := by
          simpa using (upperTriangular_walsh_nonzero_of_vanishes_on_kernel_q2 n Q a0 hker)
        simpa using
          (upperTriangular_walshSupport_card_eq_pow_rank_of_anchor_shift_q2 n r Q a0 h0 hrank))




theorem balanced_affine_count_from_walsh_support
    (n r : ℕ)
    (q : (Fin n → ZMod 2) → ZMod 2)
    (hsupport :
      Fintype.card
        {a : Fin n → ZMod 2 //
          (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
            if q x + Finset.univ.sum (fun i : Fin n => a i * x i) = 0 then
              (1 : ℤ)
            else
              (-1 : ℤ))) ≠ 0}
        = 2 ^ (2 * r))
    (hle : 2 * r ≤ n) :
    Fintype.card
      {b : (Fin n → ZMod 2) × ZMod 2 //
        (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if q x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ))) = 0}
      =
      2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1) := by
  classical
    let alpha := Fin n → ZMod 2
    let W : alpha → ℤ := fun a =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if q x + Finset.univ.sum (fun i : Fin n => a i * x i) = 0 then
          (1 : ℤ)
        else
          (-1 : ℤ))
    let S : alpha × ZMod 2 → ℤ := fun b =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if q x + Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0 then
          (1 : ℤ)
        else
          (-1 : ℤ))
    have hcard_alpha : Fintype.card alpha = 2 ^ n := by
      simp [alpha]
    have hsupportW :
        Fintype.card {a : alpha // W a ≠ 0} = 2 ^ (2 * r) := by
      simpa [alpha, W] using hsupport
    have htoggle : ∀ y : ZMod 2,
        (if y + 1 = 0 then (1 : ℤ) else (-1 : ℤ)) =
          - (if y = 0 then (1 : ℤ) else (-1 : ℤ)) := by
      intro y
      fin_cases y <;> native_decide
    have hS_iff_pair : ∀ (a : alpha) (c : ZMod 2), S (a, c) = 0 ↔ W a = 0 := by
      intro a c
      have hc : c = 0 ∨ c = 1 := by
        fin_cases c
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hc with hc | hc
      · subst c
        have hsum0 : S (a, (0 : ZMod 2)) = W a := by
          unfold S W
          apply Finset.sum_congr rfl
          intro x hx
          rw [add_zero]
        rw [hsum0]
      · subst c
        have hsum1 : S (a, (1 : ZMod 2)) = - W a := by
          unfold S W
          calc
            Finset.univ.sum (fun x : Fin n → ZMod 2 =>
                if q x + Finset.univ.sum (fun i : Fin n => a i * x i) + (1 : ZMod 2) = 0 then
                  (1 : ℤ)
                else
                  (-1 : ℤ))
                = Finset.univ.sum (fun x : Fin n → ZMod 2 =>
                    - (if q x + Finset.univ.sum (fun i : Fin n => a i * x i) = 0 then
                        (1 : ℤ)
                      else
                        (-1 : ℤ))) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    exact htoggle (q x + Finset.univ.sum (fun i : Fin n => a i * x i))
            _ = - Finset.univ.sum (fun x : Fin n → ZMod 2 =>
                    if q x + Finset.univ.sum (fun i : Fin n => a i * x i) = 0 then
                      (1 : ℤ)
                    else
                      (-1 : ℤ)) := by
                    simp
        rw [hsum1, neg_eq_zero]
    have hcard_aff :
        Fintype.card {b : alpha × ZMod 2 // S b = 0} =
          Fintype.card ({a : alpha // W a = 0} × ZMod 2) := by
      let e : {b : alpha × ZMod 2 // S b = 0} ≃ {a : alpha // W a = 0} × ZMod 2 :=
        { toFun := fun b =>
            (⟨b.1.1, (hS_iff_pair b.1.1 b.1.2).mp b.2⟩, b.1.2)
          invFun := fun p =>
            ⟨(p.1.1, p.2), (hS_iff_pair p.1.1 p.2).mpr p.1.2⟩
          left_inv := by
            intro b
            cases b with
            | mk val property =>
              cases val with
              | mk a c =>
                simp
          right_inv := by
            intro p
            cases p with
            | mk a0 c =>
              cases a0 with
              | mk a ha =>
                simp }
      exact Fintype.card_congr e
    have hzero_card :
        Fintype.card {a : alpha // W a = 0} = 2 ^ n - 2 ^ (2 * r) := by
      have hcompl :
          Fintype.card {a : alpha // W a = 0} =
            Fintype.card {a : alpha // ¬ W a ≠ 0} := by
        apply Fintype.card_congr
        exact
          { toFun := fun a => ⟨a.1, by simpa using a.2⟩
            invFun := fun a => ⟨a.1, by simpa using a.2⟩
            left_inv := by
              intro a
              cases a
              simp
            right_inv := by
              intro a
              cases a
              simp }
      calc
        Fintype.card {a : alpha // W a = 0}
            = Fintype.card {a : alpha // ¬ W a ≠ 0} := hcompl
        _ = Fintype.card alpha - Fintype.card {a : alpha // W a ≠ 0} := by
            simpa using (Fintype.card_subtype_compl (p := fun a : alpha => W a ≠ 0))
        _ = 2 ^ n - 2 ^ (2 * r) := by
            rw [hcard_alpha, hsupportW]
    have harith : (2 ^ n - 2 ^ (2 * r)) * 2 =
        2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1) := by
      have hpow_split : 2 ^ n = 2 ^ (2 * r) * 2 ^ (n - 2 * r) := by
        rw [← pow_add]
        rw [Nat.add_sub_of_le hle]
      calc
        (2 ^ n - 2 ^ (2 * r)) * 2
            = (2 ^ (2 * r) * 2 ^ (n - 2 * r) - 2 ^ (2 * r)) * 2 := by
                rw [hpow_split]
        _ = (2 ^ (2 * r) * (2 ^ (n - 2 * r) - 1)) * 2 := by
                rw [Nat.mul_sub_left_distrib, mul_one]
        _ = 2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1) := by
                rw [pow_add, pow_one]
                ac_rfl
    have hmain :
        Fintype.card {b : alpha × ZMod 2 // S b = 0} =
          2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1) := by
      calc
        Fintype.card {b : alpha × ZMod 2 // S b = 0}
            = Fintype.card ({a : alpha // W a = 0} × ZMod 2) := hcard_aff
        _ = Fintype.card {a : alpha // W a = 0} * Fintype.card (ZMod 2) := by
            rw [Fintype.card_prod]
        _ = (2 ^ n - 2 ^ (2 * r)) * 2 := by
            rw [hzero_card]
            norm_num [ZMod.card]
        _ = 2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1) := harith
    simpa [alpha, S] using hmain






theorem alternatingmatrix_tolinrank_range_finrank_le_q2
    (n : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) ≤ n := by
  classical
  calc
    Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) ≤
        Module.finrank (ZMod 2) (Fin n → ZMod 2) := by
      exact LinearMap.finrank_range_le (A.toLin')
    _ = n := by
      simp


theorem reflected_matrix_rank_le_card_q2
    (n : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) :
    Module.finrank (ZMod 2)
      (LinearMap.range
        (Matrix.toLin'
          ((fun i j : Fin n =>
            if h : (i : ℕ) < (j : ℕ) then
              Q i ⟨j, h⟩
            else if h' : (j : ℕ) < (i : ℕ) then
              Q j ⟨i, h'⟩
            else
              0) : Matrix (Fin n) (Fin n) (ZMod 2)))) ≤ n := by
  exact alternatingmatrix_tolinrank_range_finrank_le_q2 n
    ((fun i j : Fin n =>
      if h : (i : ℕ) < (j : ℕ) then
        Q i ⟨j, h⟩
      else if h' : (j : ℕ) < (i : ℕ) then
        Q j ⟨i, h'⟩
      else
        0) : Matrix (Fin n) (Fin n) (ZMod 2))




theorem rank_even_bound_from_reflected_rank_q2
    (n r : Nat)
    (Q : (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2)
    (hrank :
      Module.finrank (ZMod 2)
        (LinearMap.range
          (Matrix.toLin'
            ((fun i j : Fin n =>
              if h : (i : Nat) < (j : Nat) then
                Q i (Subtype.mk j h)
              else if h' : (j : Nat) < (i : Nat) then
                Q j (Subtype.mk i h')
              else
                0) : Matrix (Fin n) (Fin n) (ZMod 2)))) = 2 * r) :
    2 * r <= n := by
  rw [← hrank]
  exact reflected_matrix_rank_le_card_q2 n Q


theorem upperTriangular_fixedQuadratic_balancedAffineParam_card_eq_rankWeight_q2
    (n r : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (hQ_rank :
      Module.finrank (ZMod 2)
        (LinearMap.range
          (Matrix.toLin'
            (((fun i j : Fin n =>
              if h : (i : ℕ) < (j : ℕ) then
                Q i ⟨j, h⟩
              else if h' : (j : ℕ) < (i : ℕ) then
                Q j ⟨i, h'⟩
              else
                0) : Matrix (Fin n) (Fin n) (ZMod 2))))) = 2 * r) :
    Fintype.card
      {b : (Fin n → ZMod 2) × ZMod 2 //
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if
            (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                Q i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0) then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0}
      = 2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1) := by
  have hsupport :=
    upperTriangular_walshSupport_card_eq_pow_rank_unconditional_q2 n r Q hQ_rank
  have hrank_bound : 2 * r ≤ n :=
    rank_even_bound_from_reflected_rank_q2 n r Q hQ_rank
  exact
    balanced_affine_count_from_walsh_support n r
      (fun x : Fin n → ZMod 2 =>
        Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            Q i j * x i * x j.1)))
      hsupport hrank_bound




theorem upper_triangular_nonzero_balanced_affine_param_card_eq_halfrank_sum_q2
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hhalf :
      ∀ Q :
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  Q.1 i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  Q.1 j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (halfRank Q : ℕ)) :
    (let Quad :=
      (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let AffineParam := (Fin n → ZMod 2) × ZMod 2;
     let BalancedAffineParam : Quad → AffineParam → Prop := fun Q b =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0)
        then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0;
     Fintype.card
       {p : {Q : Quad // Q ≠ 0} × AffineParam //
         BalancedAffineParam p.1.1 p.2}
      =
     Finset.univ.sum (fun Q : {Q : Quad // Q ≠ 0} =>
       2 ^ (2 * (halfRank Q : ℕ) + 1) *
         (2 ^ (n - 2 * (halfRank Q : ℕ)) - 1))) := by
  classical
    dsimp only
    rw [upper_triangular_nonzero_balanced_affine_param_card_eq_sum_fibers_q2 n]
    apply Finset.sum_congr
    · rfl
    · intro Q hQ
      simpa using
        (upperTriangular_fixedQuadratic_balancedAffineParam_card_eq_rankWeight_q2
          n (halfRank Q : ℕ) Q.1 (hhalf Q))















theorem upper_triangular_nonzero_balanced_affine_param_card_add_affine_eq_halfrank_fiber_sum_q2
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hhalf :
      ∀ Q :
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  Q.1 i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  Q.1 j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (halfRank Q : ℕ)) :
    (let Quad :=
      (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let AffineParam := (Fin n → ZMod 2) × ZMod 2;
     let BalancedAffineParam : Quad → AffineParam → Prop := fun Q b =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0)
        then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0;
     Fintype.card
       {p : {Q : Quad // Q ≠ 0} × AffineParam //
         BalancedAffineParam p.1.1 p.2}
       + 2 * (2 ^ n - 1)
      =
     Finset.univ.sum (fun s : Fin (n + 1) =>
       Fintype.card {Q : {Q : Quad // Q ≠ 0} // halfRank Q = s} *
         (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))) +
       2 * (2 ^ n - 1)) := by
  classical
  dsimp
  rw [upper_triangular_nonzero_balanced_affine_param_card_eq_halfrank_sum_q2 n halfRank hhalf]
  simpa using
    (nonzeroQuadratic_rankWeight_sum_grouped_by_halfRankFiber_add_affine n halfRank)








theorem upper_triangular_reflected_rank_fiber_pred_iff_halfrank
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hrank :
      ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  (Subtype.val Q) i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  (Subtype.val Q) j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (halfRank Q : ℕ))
    (r : Fin (n + 1))
    (Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0}) :
    halfRank Q = r ↔
      Module.finrank (ZMod 2)
        (LinearMap.range
          (Matrix.toLin'
            (((fun i j : Fin n =>
              if h : (i : ℕ) < (j : ℕ) then
                (Subtype.val Q) i ⟨j, h⟩
              else if h' : (j : ℕ) < (i : ℕ) then
                (Subtype.val Q) j ⟨i, h'⟩
              else
                0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
        2 * (r : ℕ) := by
  constructor
  · intro h
    simp [hrank Q, h]
  · intro h
    apply Fin.ext
    have htwo : 2 * (halfRank Q : ℕ) = 2 * (r : ℕ) := by
      simpa [hrank Q] using h
    omega




theorem nonzero_quadratic_halfrank_subtype_card_congr_of_iff
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (r : Fin (n + 1))
    (rankPred :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Prop)
    [DecidablePred rankPred]
    (h :
      ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        halfRank Q = r ↔ rankPred Q) :
    Fintype.card
      {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
        halfRank Q = r}
      =
    Fintype.card
      {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
        rankPred Q} := by
  classical
  exact
    Fintype.card_congr
      { toFun := fun Q => ⟨Q.1, (h Q.1).1 Q.2⟩
        invFun := fun Q => ⟨Q.1, (h Q.1).2 Q.2⟩
        left_inv := by
          intro Q
          apply Subtype.ext
          rfl
        right_inv := by
          intro Q
          apply Subtype.ext
          rfl }


theorem upper_triangular_nonzero_reflected_halfRank_fiber_card_eq_rank_fiber_q2
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hrank :
      ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  (Subtype.val Q) i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  (Subtype.val Q) j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (halfRank Q : ℕ))
    (r : Fin (n + 1)) :
    Fintype.card
      {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
        halfRank Q = r}
      =
    Fintype.card
      {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  (Subtype.val Q) i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  (Subtype.val Q) j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (r : ℕ)} := by
  classical
    let rankPred :
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} → Prop :=
      fun Q =>
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  (Subtype.val Q) i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  (Subtype.val Q) j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (r : ℕ)
    simpa [rankPred] using
      (nonzero_quadratic_halfrank_subtype_card_congr_of_iff n halfRank r rankPred
        (fun Q => upper_triangular_reflected_rank_fiber_pred_iff_halfrank n halfRank hrank r Q))




theorem upper_triangular_nonzero_reflected_halfrank_weighted_summand_eq_rank_weight_q2
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hrank :
      ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  (Subtype.val Q) i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  (Subtype.val Q) j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (halfRank Q : ℕ))
    (s : Fin (n + 1)) :
    Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          halfRank Q = s} *
        (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)) =
    Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          Module.finrank (ZMod 2)
            (LinearMap.range
              (Matrix.toLin'
                (((fun i j : Fin n =>
                  if h : (i : ℕ) < (j : ℕ) then
                    (Subtype.val Q) i ⟨j, h⟩
                  else if h' : (j : ℕ) < (i : ℕ) then
                    (Subtype.val Q) j ⟨i, h'⟩
                  else
                    0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
            2 * (s : ℕ)} *
        (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)) := by
  classical
  rw [upper_triangular_nonzero_reflected_halfRank_fiber_card_eq_rank_fiber_q2 n halfRank hrank s]




theorem upper_triangular_nonzero_reflected_halfrank_weighted_fin_sum_eq_rank_range_sum_q2
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hrank :
      ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  (Subtype.val Q) i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  (Subtype.val Q) j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (halfRank Q : ℕ)) :
    (Finset.univ.sum (fun s : Fin (n + 1) =>
      Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          halfRank Q = s} *
        (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)))) =
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          Module.finrank (ZMod 2)
            (LinearMap.range
              (Matrix.toLin'
                (((fun i j : Fin n =>
                  if h : (i : ℕ) < (j : ℕ) then
                    (Subtype.val Q) i ⟨j, h⟩
                  else if h' : (j : ℕ) < (i : ℕ) then
                    (Subtype.val Q) j ⟨i, h'⟩
                  else
                    0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
            2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) := by
  classical
  let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2
  let NonzeroQuad := {Q : Quad // Q ≠ 0}
  let rankOf : NonzeroQuad → ℕ := fun Q =>
    Module.finrank (ZMod 2)
      (LinearMap.range
        (Matrix.toLin'
          (((fun i j : Fin n =>
            if h : (i : ℕ) < (j : ℕ) then
              (Subtype.val Q) i ⟨j, h⟩
            else if h' : (j : ℕ) < (i : ℕ) then
              (Subtype.val Q) j ⟨i, h'⟩
            else
              0) : Matrix (Fin n) (Fin n) (ZMod 2)))))
  let left : Fin (n + 1) → ℕ := fun s =>
    Fintype.card {Q : NonzeroQuad // halfRank Q = s} *
      (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))
  let right : ℕ → ℕ := fun r =>
    Fintype.card {Q : NonzeroQuad // rankOf Q = 2 * r} *
      (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))
  change (Finset.univ.sum left) = (Finset.range (n + 1)).sum right
  trans Finset.univ.sum (fun s : Fin (n + 1) => right (s : ℕ))
  · apply Finset.sum_congr
    · rfl
    · intro s _
      have hcard :
          Fintype.card {Q : NonzeroQuad // halfRank Q = s} =
            Fintype.card {Q : NonzeroQuad // rankOf Q = 2 * (s : ℕ)} := by
        simpa [rankOf, NonzeroQuad, Quad] using
          upper_triangular_nonzero_reflected_halfRank_fiber_card_eq_rank_fiber_q2
            n halfRank hrank s
      simpa [left, right] using
        congrArg
          (fun c : ℕ =>
            c * (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1)))
          hcard
  · rw [Fin.sum_univ_eq_sum_range]


theorem upper_triangular_nonzero_reflected_halfRank_weighted_sum_eq_rank_weight_sum_q2
    (n : ℕ)
    (halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1))
    (hrank :
      ∀ Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              (((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  (Subtype.val Q) i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  (Subtype.val Q) j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
          2 * (halfRank Q : ℕ)) :
    Finset.univ.sum (fun s : Fin (n + 1) =>
      Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          halfRank Q = s} *
        (2 ^ (2 * (s : ℕ) + 1) * (2 ^ (n - 2 * (s : ℕ)) - 1))) +
      2 * (2 ^ n - 1) =
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      Fintype.card
        {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
          Module.finrank (ZMod 2)
            (LinearMap.range
              (Matrix.toLin'
                (((fun i j : Fin n =>
                  if h : (i : ℕ) < (j : ℕ) then
                    (Subtype.val Q) i ⟨j, h⟩
                  else if h' : (j : ℕ) < (i : ℕ) then
                    (Subtype.val Q) j ⟨i, h'⟩
                  else
                    0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
            2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) +
      2 * (2 ^ n - 1) := by
  exact congrArg (fun x : ℕ => x + 2 * (2 ^ n - 1))
      (upper_triangular_nonzero_reflected_halfrank_weighted_fin_sum_eq_rank_range_sum_q2 n halfRank hrank)








theorem matrix_tolin_kernel_finrank_eq_succ_of_two_mul_two_pow_eq
    (m n : ℕ)
    (A : Matrix (Fin m) (Fin m) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hpow :
      2 * 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) =
        2 ^ Module.finrank (ZMod 2) (LinearMap.ker (B.toLin'))) :
    Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) =
      Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) + 1 := by
  classical
    let a := Module.finrank (ZMod 2) (LinearMap.ker (A.toLin'))
    let b := Module.finrank (ZMod 2) (LinearMap.ker (B.toLin'))
    have hpow' : 2 ^ (a + 1) = 2 ^ b := by
      dsimp [a, b]
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hpow
    have hinj : Function.Injective (fun k : ℕ => 2 ^ k) :=
      Nat.pow_right_injective (by norm_num : 1 < 2)
    simpa [a, b] using (hinj hpow').symm




theorem matrix_tolin_kernel_subtype_card_eq_two_pow_finrank
    (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Fintype.card {z : Fin n → ZMod 2 // A.toLin' z = 0} =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) := by
  classical
    let e : {z : Fin n → ZMod 2 // A.toLin' z = 0} ≃ LinearMap.ker (A.toLin') :=
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := by
          intro z
          ext
          rfl
        right_inv := by
          intro z
          ext
          rfl }
    calc
      Fintype.card {z : Fin n → ZMod 2 // A.toLin' z = 0}
          = Fintype.card (LinearMap.ker (A.toLin')) := Fintype.card_congr e
      _ = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) := by
        simpa using
          (Module.card_fintype
            (Module.finBasis (ZMod 2) (LinearMap.ker (A.toLin'))))
      _ = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) := by
        norm_num [ZMod.card]


theorem matrix_tolin_kernel_finrank_succ_of_two_mul_kernel_card
    (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2))
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hcard :
      2 * Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0} =
        Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0}) :
    Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) =
      Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) + 1 := by
  classical
    apply matrix_tolin_kernel_finrank_eq_succ_of_two_mul_two_pow_eq (n + 1) n A B
    calc
      2 * 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (A.toLin'))
          = 2 * Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0} := by
            rw [matrix_tolin_kernel_subtype_card_eq_two_pow_finrank]
      _ = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := hcard
      _ = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) := by
            rw [matrix_tolin_kernel_subtype_card_eq_two_pow_finrank]








theorem border_matrix_tolin_castsucc_apply
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v w : Fin n → ZMod 2) (t : ZMod 2) (i : Fin n) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun r c =>
        (if hr : (r : ℕ) < n then
          (if hc : (c : ℕ) < n then
            B ⟨(r : ℕ), hr⟩ ⟨(c : ℕ), hc⟩
          else
            v ⟨(r : ℕ), hr⟩)
        else
          (if hc : (c : ℕ) < n then
            v ⟨(c : ℕ), hc⟩
          else
            0));
     let z : Fin (n + 1) → ZMod 2 :=
      fun k =>
        (if hk : (k : ℕ) < n then
          w ⟨(k : ℕ), hk⟩
        else
          t);
     A.toLin' z (Fin.castSucc i) = (B.toLin' w) i + v i * t) := by
  classical
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    simp




theorem border_matrix_tolin_last_apply
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v w : Fin n → ZMod 2) (t : ZMod 2) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun r c =>
        (if hr : (r : ℕ) < n then
          (if hc : (c : ℕ) < n then
            B ⟨(r : ℕ), hr⟩ ⟨(c : ℕ), hc⟩
          else
            v ⟨(r : ℕ), hr⟩)
        else
          (if hc : (c : ℕ) < n then
            v ⟨(c : ℕ), hc⟩
          else
            0));
     let z : Fin (n + 1) → ZMod 2 :=
      fun k =>
        (if hk : (k : ℕ) < n then
          w ⟨(k : ℕ), hk⟩
        else
          t);
     A.toLin' z (Fin.last n) = Finset.univ.sum (fun i : Fin n => v i * w i)) := by
  classical
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_castSucc]
    simp [mul_comm]


theorem borderMatrix_kernel_card_eq_borderBlock_kernel_card
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            v ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            v ⟨(j : ℕ), hj⟩
          else
            0;
     Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0} =
      Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • v = 0 ∧
          Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}) := by
  classical
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j => if hi : (i : ℕ) < n then if hj : (j : ℕ) < n then B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else v ⟨(i : ℕ), hi⟩ else if hj : (j : ℕ) < n then v ⟨(j : ℕ), hj⟩ else 0
  let split : (Fin (n + 1) → ZMod 2) → (Fin n → ZMod 2) × ZMod 2 := fun z => (fun i : Fin n => z (Fin.castSucc i), z (Fin.last n))
  let glue : ((Fin n → ZMod 2) × ZMod 2) → Fin (n + 1) → ZMod 2 := fun wt i => if hi : (i : ℕ) < n then wt.1 ⟨(i : ℕ), hi⟩ else wt.2
  have h_glue_split : ∀ z : Fin (n + 1) → ZMod 2, glue (split z) = z := by
    intro z
    funext i
    by_cases hi : (i : ℕ) < n
    · have hcast : Fin.castSucc (⟨(i : ℕ), hi⟩ : Fin n) = i := by
        ext
        rfl
      simp [glue, split, hi, hcast]
    · have hval : (i : ℕ) = n := by
        omega
      have hlast : i = Fin.last n := by
        ext
        exact hval
      simp [glue, split, hlast]
  have h_split_glue : ∀ wt : (Fin n → ZMod 2) × ZMod 2, split (glue wt) = wt := by
    intro wt
    cases wt with
    | mk w t =>
        apply Prod.ext
        · funext i
          simp [split, glue]
        · simp [split, glue]
  have hRow : ∀ (wt : (Fin n → ZMod 2) × ZMod 2) (i : Fin n), (A.toLin' (glue wt)) (Fin.castSucc i) = (B.toLin' wt.1 + wt.2 • v) i := by
    rintro ⟨w, t⟩ i
    simpa [A, glue, mul_comm] using border_matrix_tolin_castsucc_apply n B v w t i
  have hLast : ∀ wt : (Fin n → ZMod 2) × ZMod 2, (A.toLin' (glue wt)) (Fin.last n) = Finset.univ.sum (fun i : Fin n => v i * wt.1 i) := by
    rintro ⟨w, t⟩
    simpa [A, glue] using border_matrix_tolin_last_apply n B v w t
  have hPred : ∀ wt : (Fin n → ZMod 2) × ZMod 2, A.toLin' (glue wt) = 0 ↔ B.toLin' wt.1 + wt.2 • v = 0 ∧ Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0 := by
    intro wt
    constructor
    · intro hA
      constructor
      · funext i
        have h := congrFun hA (Fin.castSucc i)
        simpa [hRow wt i] using h
      · have h := congrFun hA (Fin.last n)
        simpa [hLast wt] using h
    · intro hQ
      funext i
      by_cases hi : (i : ℕ) < n
      · have hidx : Fin.castSucc (⟨(i : ℕ), hi⟩ : Fin n) = i := by
          ext
          rfl
        have h := congrFun hQ.1 (⟨(i : ℕ), hi⟩ : Fin n)
        rw [← hidx]
        rw [hRow wt (⟨(i : ℕ), hi⟩ : Fin n)]
        simpa using h
      · have hval : (i : ℕ) = n := by
          omega
        have hidx : i = Fin.last n := by
          ext
          exact hval
        rw [hidx]
        rw [hLast wt]
        simpa using hQ.2
  have hcard : Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0} = Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 // B.toLin' wt.1 + wt.2 • v = 0 ∧ Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0} := by
    exact Fintype.card_congr
      { toFun := fun z =>
          ⟨split z.1,
            by
              have hz : A.toLin' (glue (split z.1)) = 0 := by
                simp [h_glue_split z.1, z.2]
              exact (hPred (split z.1)).1 hz⟩
        invFun := fun wt =>
          ⟨glue wt.1,
            by
              exact (hPred wt.1).2 wt.2⟩
        left_inv := by
          intro z
          apply Subtype.ext
          exact h_glue_split z.1
        right_inv := by
          intro wt
          apply Subtype.ext
          exact h_split_glue wt.1 }
  simpa [A] using hcard












theorem border_block_kernel_card_eq_of_not_range_membership
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2)
    (hv : v ∉ LinearMap.range (B.toLin')) :
    2 * Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • v = 0 ∧
          Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
        = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
  rcases exists_tolin_kernel_dot_one_of_not_mem_range n B hsymm v hv with ⟨z, hzker, hzdot⟩; simpa using borderBlock_kernel_card_eq_of_notRangeWitness n B hdiag hsymm v z hzker hzdot




theorem border_matrix_two_mul_kernel_card_transport
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) {C : ℕ}
    (hcard :
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              v ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              v ⟨(j : ℕ), hj⟩
            else
              0;
       Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0}) = C) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            v ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            v ⟨(j : ℕ), hj⟩
          else
            0;
     2 * Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0}) = 2 * C := by
  exact congrArg (fun m : ℕ => 2 * m) hcard




theorem border_matrix_kernel_card_eq_of_count_bridge
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) {C : ℕ}
    (hcard :
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              v ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              v ⟨(j : ℕ), hj⟩
            else
              0;
       Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0}) = C)
    (hblock :
      2 * C = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0}) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            v ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            v ⟨(j : ℕ), hj⟩
          else
            0;
     2 * Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0}) =
      Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
  exact (border_matrix_two_mul_kernel_card_transport n B v hcard).trans hblock


theorem borderMatrix_kernel_card_eq_of_not_range_membership
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2)
    (hv : v ∉ LinearMap.range (B.toLin')) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            v ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            v ⟨(j : ℕ), hj⟩
          else
            0;
     2 * Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0} =
      Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0}) := by
  exact border_matrix_kernel_card_eq_of_count_bridge n B v
    (borderMatrix_kernel_card_eq_borderBlock_kernel_card n B v)
    (border_block_kernel_card_eq_of_not_range_membership n B hdiag hsymm v hv)










theorem border_block_kernel_card_eq_of_range_membership
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2)
    (hv : v ∈ LinearMap.range (B.toLin')) :
    Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • v = 0 ∧
          Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
        = 2 * Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
  rcases hv with ⟨u, rfl⟩
  simpa using borderBlock_kernel_card_eq_of_rangeVector n B hdiag hsymm u




theorem borderBlock_kernel_card_range_dichotomy
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2) :
    (v ∈ LinearMap.range (B.toLin') →
      Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • v = 0 ∧
          Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
        = 2 * Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0}) ∧
    (v ∉ LinearMap.range (B.toLin') →
      2 * Fintype.card {wt : (Fin n → ZMod 2) × ZMod 2 //
        B.toLin' wt.1 + wt.2 • v = 0 ∧
          Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
        = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0}) := by
  exact And.intro
      (fun hv => by
        rcases hv with ⟨u, rfl⟩
        exact borderBlock_kernel_card_eq_of_rangeVector n B hdiag hsymm u)
      (fun hv => by
        rcases exists_tolin_kernel_dot_one_of_not_mem_range n B hsymm v hv with ⟨z, hz, hdot⟩
        exact borderBlock_kernel_card_eq_of_notRangeWitness n B hdiag hsymm v z hz hdot)




theorem border_block_to_lin_witness_shift
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v x y : Fin n → ZMod 2) (t : ZMod 2)
    (hx : B.toLin' x = v) :
    B.toLin' (y + t • x) + t • v = B.toLin' y := by
  classical
    rw [map_add, map_smul, hx]
    ext i
    change (((B.toLin' y) i + t * v i) + t * v i = (B.toLin' y) i)
    have htwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    rw [add_assoc, ← two_mul, htwo]
    simp




theorem border_block_witness_shift_last_coordinate
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v x k : Fin n → ZMod 2)
    (hx : B.toLin' x = v)
    (hk : B.toLin' k = 0)
    (t : ZMod 2) :
    (Finset.univ.sum (fun i : Fin n => v i * ((k + t • x) i))) = 0 := by
  classical
      have hx_apply : ∀ i : Fin n, v i = Finset.univ.sum (fun j : Fin n => B i j * x j) := by
        intro i
        simpa only [Matrix.toLin'_apply, Matrix.mulVec] using (congrFun hx.symm i)
      have hk_apply : ∀ i : Fin n, Finset.univ.sum (fun j : Fin n => B i j * k j) = 0 := by
        intro i
        simpa only [Matrix.toLin'_apply, Matrix.mulVec, Pi.zero_apply] using (congrFun hk i)
      let F : Fin n → Fin n → ZMod 2 := fun i j => B i j * x j * x i
      have hF_symm : ∀ i j : Fin n, F i j = F j i := by
        intro i j
        dsimp [F]
        rw [hsymm i j]
        ring
      have hF_diag : ∀ i : Fin n, F i i = 0 := by
        intro i
        dsimp [F]
        rw [hdiag i]
        simp
      have hquad_on : ∀ s : Finset (Fin n), s.sum (fun i => s.sum (fun j => F i j)) = 0 := by
        intro s
        exact Finset.induction_on s (by simp) (by
          intro a s ha ih
          have hcross : s.sum (fun j => F a j) = s.sum (fun i => F i a) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hF_symm a i
          have hcross_zero : s.sum (fun j => F a j) + s.sum (fun i => F i a) = 0 := by
            rw [hcross]
            have htwo : (2 : ZMod 2) = 0 := by
              decide
            calc
              s.sum (fun i => F i a) + s.sum (fun i => F i a)
                  = (2 : ZMod 2) * s.sum (fun i => F i a) := by
                    ring
              _ = 0 := by
                    rw [htwo]
                    simp
          calc
            (insert a s).sum (fun i => (insert a s).sum (fun j => F i j))
                = (F a a + s.sum (fun j => F a j)) +
                    s.sum (fun i => F i a + s.sum (fun j => F i j)) := by
                  simp [Finset.sum_insert, ha]
            _ = F a a + (s.sum (fun j => F a j) + s.sum (fun i => F i a)) +
                    s.sum (fun i => s.sum (fun j => F i j)) := by
                  rw [Finset.sum_add_distrib]
                  ring
            _ = 0 := by
                  rw [hF_diag a, hcross_zero, ih]
                  ring)
      have hdot_vk : Finset.univ.sum (fun i : Fin n => v i * k i) = 0 := by
        calc
          Finset.univ.sum (fun i : Fin n => v i * k i)
              = Finset.univ.sum (fun i : Fin n =>
                  (Finset.univ.sum (fun j : Fin n => B i j * x j)) * k i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hx_apply i]
          _ = Finset.univ.sum (fun i : Fin n =>
                  Finset.univ.sum (fun j : Fin n => (B i j * x j) * k i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_mul]
          _ = Finset.univ.sum (fun j : Fin n =>
                  Finset.univ.sum (fun i : Fin n => (B i j * x j) * k i)) := by
                rw [Finset.sum_comm]
          _ = Finset.univ.sum (fun j : Fin n =>
                  x j * Finset.univ.sum (fun i : Fin n => B j i * k i)) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                rw [hsymm i j]
                ring
          _ = 0 := by
                simp [hk_apply]
      have hdot_vx : Finset.univ.sum (fun i : Fin n => v i * x i) = 0 := by
        calc
          Finset.univ.sum (fun i : Fin n => v i * x i)
              = Finset.univ.sum (fun i : Fin n =>
                  (Finset.univ.sum (fun j : Fin n => B i j * x j)) * x i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hx_apply i]
          _ = Finset.univ.sum (fun i : Fin n =>
                  Finset.univ.sum (fun j : Fin n => F i j)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.sum_mul]
          _ = 0 := by
                simpa using hquad_on Finset.univ
      calc
        Finset.univ.sum (fun i : Fin n => v i * ((k + t • x) i))
            = Finset.univ.sum (fun i : Fin n => v i * k i + v i * (t * x i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [mul_add]
        _ = Finset.univ.sum (fun i : Fin n => v i * k i) +
            Finset.univ.sum (fun i : Fin n => v i * (t * x i)) := by
              rw [Finset.sum_add_distrib]
        _ = Finset.univ.sum (fun i : Fin n => v i * k i) +
            t * Finset.univ.sum (fun i : Fin n => v i * x i) := by
              apply congrArg (fun z => Finset.univ.sum (fun i : Fin n => v i * k i) + z)
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = 0 := by
              simp [hdot_vk, hdot_vx]








theorem borderMatrix_kernel_card_eq_of_range_membership
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2)
    (hv : v ∈ LinearMap.range (B.toLin')) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            v ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            v ⟨(j : ℕ), hj⟩
          else
            0;
     Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0} =
      2 * Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0}) := by
  classical
  exact (borderMatrix_kernel_card_eq_borderBlock_kernel_card n B v).trans (by
    rcases hv with ⟨x, hx⟩
    let K := {z : Fin n → ZMod 2 // B.toLin' z = 0}
    let C := {wt : (Fin n → ZMod 2) × ZMod 2 //
      B.toLin' wt.1 + wt.2 • v = 0 ∧
        Finset.univ.sum (fun i : Fin n => v i * wt.1 i) = 0}
    change Fintype.card C = 2 * Fintype.card K
    have hchar : (2 : ZMod 2) = 0 := by
      exact ZMod.natCast_self 2
    have hdouble (y : Fin n → ZMod 2) (t : ZMod 2) :
        (y + t • x) + t • x = y := by
      ext i
      calc
        ((y + t • x) + t • x) i = (y i + t • x i) + t • x i := by
          simp [Pi.add_apply, Pi.smul_apply]
        _ = y i + ((t • x i) + t • x i) := by
          rw [add_assoc]
        _ = y i + (2 : ZMod 2) * (t • x i) := by
          rw [← two_mul (t • x i)]
        _ = y i := by
          simp [hchar]
    let e : K × ZMod 2 ≃ C :=
      { toFun := fun p =>
          ⟨(p.1.1 + p.2 • x, p.2), by
            constructor
            · have htop := border_block_to_lin_witness_shift n B v x p.1.1 p.2 hx
              simpa [p.1.2] using htop
            · exact border_block_witness_shift_last_coordinate n B hdiag hsymm v x p.1.1 hx p.1.2 p.2⟩
        invFun := fun c =>
          (⟨c.1.1 + c.1.2 • x, by
            have hshift :=
              (border_block_to_lin_witness_shift n B v x
                (c.1.1 + c.1.2 • x) c.1.2 hx).symm
            rw [hdouble c.1.1 c.1.2] at hshift
            exact hshift.trans c.2.1⟩, c.1.2)
        left_inv := by
          intro p
          apply Prod.ext
          · apply Subtype.ext
            exact hdouble p.1.1 p.2
          · rfl
        right_inv := by
          intro c
          apply Subtype.ext
          apply Prod.ext
          · exact hdouble c.1.1 c.1.2
          · rfl }
    simpa [Fintype.card_prod, Nat.mul_comm] using (Fintype.card_congr e).symm)










theorem borderMatrix_toLinRank_eq_of_range_membership
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2)
    (hv : v ∈ LinearMap.range (B.toLin')) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            v ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            v ⟨(j : ℕ), hj⟩
          else
            0;
     Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) =
      Module.finrank (ZMod 2) (LinearMap.range (B.toLin'))) := by
  classical
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j => if hi : (i : ℕ) < n then if hj : (j : ℕ) < n then B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else v ⟨(i : ℕ), hi⟩ else if hj : (j : ℕ) < n then v ⟨(j : ℕ), hj⟩ else 0
    have hcard_sub := borderMatrix_kernel_card_eq_of_range_membership n B hdiag hsymm v hv
    have hcard : Fintype.card (LinearMap.ker (A.toLin')) = 2 * Fintype.card (LinearMap.ker (B.toLin')) := by
      simpa [A, LinearMap.mem_ker] using hcard_sub
    have hker : Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) = Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) + 1 := by
      have hcardA : Fintype.card (LinearMap.ker (A.toLin')) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) := by
        simpa using
          (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker (A.toLin')))
      have hcardB : Fintype.card (LinearMap.ker (B.toLin')) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) := by
        simpa using
          (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker (B.toLin')))
      have hpow : 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) = 2 ^ (Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) + 1) := by
        rw [← hcardA, hcard, hcardB]
        rw [pow_succ]
        ring
      exact Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ)) hpow
    have hrnA : Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) + Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) = n + 1 := by
      simpa using (LinearMap.finrank_range_add_finrank_ker (A.toLin'))
    have hrnB : Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) + Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) = n := by
      simpa using (LinearMap.finrank_range_add_finrank_ker (B.toLin'))
    have hrange : Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) := by
      omega
    simpa [A] using hrange




theorem nat_add_right_cancel_add_two
    (rankA rankB kerA : ℕ)
    (h : rankA + kerA = rankB + kerA + 2) :
    rankA = rankB + 2 := by
  omega


theorem rank_eq_add_two_of_nullity_succ_succ
    (n rankA rankB kerA kerB : ℕ)
    (hA : rankA + kerA = n + 1)
    (hB : rankB + kerB = n)
    (hker : kerB = kerA + 1) :
    rankA = rankB + 2 := by
  exact Nat.add_right_cancel (by
      calc
        rankA + kerA = n + 1 := hA
        _ = (rankB + kerB) + 1 := by
          rw [hB]
        _ = (rankB + (kerA + 1)) + 1 := by
          rw [hker]
        _ = (rankB + 2) + kerA := by
          calc
            (rankB + (kerA + 1)) + 1
                = rankB + ((kerA + 1) + 1) := by
                  rw [Nat.add_assoc]
            _ = rankB + (kerA + (1 + 1)) := by
                  rw [Nat.add_assoc]
            _ = rankB + ((1 + 1) + kerA) := by
                  rw [Nat.add_comm kerA (1 + 1)]
            _ = rankB + (2 + kerA) := by
                  rfl
            _ = (rankB + 2) + kerA := by
                  rw [← Nat.add_assoc])


theorem borderMatrix_toLinRank_eq_add_two_of_not_range_membership
    (n : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2)
    (hv : v ∉ LinearMap.range (B.toLin')) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            v ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            v ⟨(j : ℕ), hj⟩
          else
            0;
     Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) =
      Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) + 2) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j => if hi : (i : ℕ) < n then if hj : (j : ℕ) < n then B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else v ⟨(i : ℕ), hi⟩ else if hj : (j : ℕ) < n then v ⟨(j : ℕ), hj⟩ else 0
  have hcard : 2 * Fintype.card {z : Fin (n + 1) → ZMod 2 // A.toLin' z = 0} = Fintype.card {z : Fin n → ZMod 2 // B.toLin' z = 0} := by
    simpa [A] using (borderMatrix_kernel_card_eq_of_not_range_membership n B hdiag hsymm v hv)
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) = Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) + 1 := matrix_tolin_kernel_finrank_succ_of_two_mul_kernel_card n A B hcard
  have hA : Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) + Module.finrank (ZMod 2) (LinearMap.ker (A.toLin')) = n + 1 := by
    simpa using (LinearMap.finrank_range_add_finrank_ker (A.toLin'))
  have hB : Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) + Module.finrank (ZMod 2) (LinearMap.ker (B.toLin')) = n := by
    simpa using (LinearMap.finrank_range_add_finrank_ker (B.toLin'))
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) + 2 := rank_eq_add_two_of_nullity_succ_succ n (Module.finrank (ZMod 2) (LinearMap.range (A.toLin'))) (Module.finrank (ZMod 2) (LinearMap.range (B.toLin'))) (Module.finrank (ZMod 2) (LinearMap.ker (A.toLin'))) (Module.finrank (ZMod 2) (LinearMap.ker (B.toLin'))) hA hB hker
  simpa [A] using hrank




theorem base_rank_add_two_odd_rhs_of_not_range_membership_q2
    (n r : ℕ)
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2)
    (hnot : v ∉ LinearMap.range (B.toLin')) :
    Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) + 2 = 2 * r + 1 ↔
      (Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1 ∧
        v ∈ LinearMap.range (B.toLin')) ∨
      (∃ s : ℕ,
        r = s + 1 ∧
        Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * s + 1 ∧
        v ∉ LinearMap.range (B.toLin')) := by
  exact Iff.intro
    (fun h => by
      right
      cases r with
      | zero => omega
      | succ s => exact ⟨s, by omega, by omega, hnot⟩)
    (fun h => by
      cases h with
      | inl hleft => exact False.elim (hnot hleft.2)
      | inr hright =>
          rcases hright with ⟨s, hs, hrank, hnot'⟩
          omega)













theorem base_rank_odd_rhs_of_range_membership_q2
    (n r : ℕ)
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2)
    (hv : v ∈ LinearMap.range (B.toLin')) :
    Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1 ↔
      (Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1 ∧
        v ∈ LinearMap.range (B.toLin')) ∨
      (∃ s : ℕ,
        r = s + 1 ∧
        Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * s + 1 ∧
        v ∉ LinearMap.range (B.toLin')) := by
  exact Iff.intro
      (fun h => Or.inl ⟨h, hv⟩)
      (fun h =>
        match h with
        | Or.inl hleft => hleft.1
        | Or.inr hright =>
            match hright with
            | ⟨s, hs, hrank, hnot⟩ => False.elim (hnot hv))


theorem border_rank_odd_target_iff_base_rank_membership_q2
    (n r : ℕ)
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j =>
      if hi : (i : ℕ) < n then
        if hj : (j : ℕ) < n then
          B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
        else
          v ⟨(i : ℕ), hi⟩
      else if hj : (j : ℕ) < n then
        v ⟨(j : ℕ), hj⟩
      else
        0;
     Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1) ↔
      (Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1 ∧
        v ∈ LinearMap.range (B.toLin')) ∨
      (∃ s : ℕ,
        r = s + 1 ∧
        Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * s + 1 ∧
        v ∉ LinearMap.range (B.toLin')) := by
  classical
    by_cases hv : (v ∈ (LinearMap.range (B.toLin') : Submodule (ZMod 2) (Fin n → ZMod 2)))
    · have hA :=
        borderMatrix_toLinRank_eq_of_range_membership n B hdiag hsymm v hv
      simpa [hA] using (base_rank_odd_rhs_of_range_membership_q2 n r B v hv)
    · have hA :=
        borderMatrix_toLinRank_eq_add_two_of_not_range_membership n B hdiag hsymm v hv
      simpa [hA] using (base_rank_add_two_odd_rhs_of_not_range_membership_q2 n r B v hv)




theorem card_zero_false_of_subtype_witness_q2
    (n k : ℕ)
    (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * k + 1)
    (hcard :
      Fintype.card {C : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, C i i = 0) ∧
        (∀ i j : Fin n, C i j = C j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (C.toLin')) = 2 * k + 1} = 0) :
    False := by
  classical
    have hpos :
        0 < Fintype.card {C : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, C i i = 0) ∧
          (∀ i j : Fin n, C i j = C j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (C.toLin')) = 2 * k + 1} := by
      exact Fintype.card_pos_iff.mpr ⟨⟨B, hdiag, hsymm, hrank⟩⟩
    omega




theorem border_pair_odd_rank_subtype_empty_of_base_cards_q2
    (n r : ℕ)
    (h_same :
      Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, B i i = 0) ∧
        (∀ i j : Fin n, B i j = B j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1} = 0)
    (h_pred :
      ∀ s : ℕ, r = s + 1 →
        Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * s + 1} = 0) :
    (let base : Type :=
      {B : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, B i i = 0) ∧
        (∀ i j : Fin n, B i j = B j i)};
     IsEmpty {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            p.2 ⟨(i : ℕ), hi⟩
        else if hj : (j : ℕ) < n then
          p.2 ⟨(j : ℕ), hj⟩
        else
          0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1)}) := by
  classical
  dsimp
  constructor
  intro p
  rcases p with ⟨p, hp⟩
  rcases p with ⟨B, v⟩
  rcases B with ⟨B, hBdiag, hBsymm⟩
  have hborder :=
    (border_rank_odd_target_iff_base_rank_membership_q2 n r B hBdiag hBsymm v).mp hp
  rcases hborder with hbase | hbase
  · exact card_zero_false_of_subtype_witness_q2 n r B hBdiag hBsymm hbase.1 h_same
  · rcases hbase with ⟨s, hrs, hrank⟩
    exact card_zero_false_of_subtype_witness_q2 n s B hBdiag hBsymm hrank.1 (h_pred s hrs)


theorem alternatingMatrix_borderPair_oddRank_card_zero_of_base_q2
    (n r : ℕ)
    (h_same :
      Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, B i i = 0) ∧
        (∀ i j : Fin n, B i j = B j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1} = 0)
    (h_pred :
      ∀ s : ℕ, r = s + 1 →
        Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * s + 1} = 0) :
    (let base : Type :=
      {B : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, B i i = 0) ∧
        (∀ i j : Fin n, B i j = B j i)};
     Fintype.card {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            p.2 ⟨(i : ℕ), hi⟩
        else if hj : (j : ℕ) < n then
          p.2 ⟨(j : ℕ), hj⟩
        else
          0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1)} = 0) := by
  classical
    apply Fintype.card_eq_zero_iff.mpr
    simpa using border_pair_odd_rank_subtype_empty_of_base_cards_q2 n r h_same h_pred


theorem alternatingMatrix_oddRank_stratum_card_zero_succ_of_base_q2
    (n r : ℕ)
    (h_same :
      Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, B i i = 0) ∧
        (∀ i j : Fin n, B i j = B j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1} = 0)
    (h_pred :
      ∀ s : ℕ, r = s + 1 →
        Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * s + 1} = 0) :
    Fintype.card {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
      (∀ i : Fin (n + 1), A i i = 0) ∧
      (∀ i j : Fin (n + 1), A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1} = 0 := by
  classical
  let base : Type :=
    {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i)}
  let pairStratum : Type :=
    {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            p.2 ⟨(i : ℕ), hi⟩
        else if hj : (j : ℕ) < n then
          p.2 ⟨(j : ℕ), hj⟩
        else
          0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1)}
  have hpair : Fintype.card pairStratum = 0 := by
    change Fintype.card
        {p : base × (Fin n → ZMod 2) //
          (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j =>
            if hi : (i : ℕ) < n then
              if hj : (j : ℕ) < n then
                p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
              else
                p.2 ⟨(i : ℕ), hi⟩
            else if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
           Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1)} = 0
    exact alternatingMatrix_borderPair_oddRank_card_zero_of_base_q2 n r h_same h_pred
  let borderMatrix :
      base × (Fin n → ZMod 2) →
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
    fun p i j =>
      if hi : (i : ℕ) < n then
        if hj : (j : ℕ) < n then
          p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
        else
          p.2 ⟨(i : ℕ), hi⟩
      else if hj : (j : ℕ) < n then
        p.2 ⟨(j : ℕ), hj⟩
      else
        0
  let succStratum : Type :=
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
      (∀ i : Fin (n + 1), A i i = 0) ∧
      (∀ i j : Fin (n + 1), A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1}
  have hcast :
      ∀ {i : Fin (n + 1)} (hi : (i : ℕ) < n),
        (Fin.castSucc (⟨(i : ℕ), hi⟩ : Fin n) : Fin (n + 1)) = i := by
    intro i hi
    apply Fin.ext
    rfl
  have hlast :
      ∀ {i : Fin (n + 1)}, ¬ (i : ℕ) < n → i = Fin.last n := by
    intro i hi
    apply Fin.ext
    exact Nat.le_antisymm (Nat.le_of_lt_succ i.2) (Nat.le_of_not_gt hi)
  let projPair : succStratum → base × (Fin n → ZMod 2) := fun A =>
    let B : Matrix (Fin n) (Fin n) (ZMod 2) :=
      fun i j => A.1 (Fin.castSucc i) (Fin.castSucc j)
    let hB :
        (∀ i : Fin n, B i i = 0) ∧
        (∀ i j : Fin n, B i j = B j i) := by
      constructor
      · intro i
        simpa [B] using A.2.1 (Fin.castSucc i)
      · intro i j
        simpa [B] using A.2.2.1 (Fin.castSucc i) (Fin.castSucc j)
    (⟨B, hB⟩, fun i => A.1 (Fin.castSucc i) (Fin.last n))
  have h_proj_ext : ∀ A : succStratum, borderMatrix (projPair A) = A.1 := by
    intro A
    ext i j
    by_cases hi : (i : ℕ) < n
    · by_cases hj : (j : ℕ) < n
      · have hicut := hcast (i := i) hi
        have hjcut := hcast (i := j) hj
        simp [projPair, borderMatrix, hi, hj, hicut, hjcut]
      · have hicut := hcast (i := i) hi
        have hjlast := hlast (i := j) hj
        simp [projPair, borderMatrix, hi, hicut, hjlast]
    · by_cases hj : (j : ℕ) < n
      · have hilast := hlast (i := i) hi
        have hjcut := hcast (i := j) hj
        simp [projPair, borderMatrix, hj, hilast, hjcut, A.2.2.1 j (Fin.last n)]
      · have hilast := hlast (i := i) hi
        have hjlast := hlast (i := j) hj
        simp [projPair, borderMatrix, hilast, hjlast, A.2.1 (Fin.last n)]
  let toPair : succStratum → pairStratum := fun A =>
    ⟨projPair A, by
      have hA : borderMatrix (projPair A) = A.1 := h_proj_ext A
      change Module.finrank (ZMod 2) (LinearMap.range ((borderMatrix (projPair A)).toLin')) = 2 * r + 1
      rw [hA]
      exact A.2.2.2⟩
  let ofPair : pairStratum → succStratum := fun p =>
    ⟨borderMatrix p.1, by
      constructor
      · intro i
        by_cases hi : (i : ℕ) < n
        · simpa [borderMatrix, hi] using p.1.1.2.1 ⟨(i : ℕ), hi⟩
        · simp [borderMatrix, hi]
      · constructor
        · intro i j
          by_cases hi : (i : ℕ) < n
          · by_cases hj : (j : ℕ) < n
            · simpa [borderMatrix, hi, hj] using
                p.1.1.2.2 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            · simp [borderMatrix, hi, hj]
          · by_cases hj : (j : ℕ) < n
            · simp [borderMatrix, hi, hj]
            · simp [borderMatrix, hi, hj]
        · change Module.finrank (ZMod 2) (LinearMap.range ((borderMatrix p.1).toLin')) = 2 * r + 1
          exact p.2⟩
  have h_left : Function.LeftInverse ofPair toPair := by
    intro A
    apply Subtype.ext
    change borderMatrix (projPair A) = A.1
    exact h_proj_ext A
  have h_right : Function.RightInverse ofPair toPair := by
    intro p
    apply Subtype.ext
    change projPair (ofPair p) = p.1
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp [projPair, ofPair, borderMatrix]
    · funext i
      simp [projPair, ofPair, borderMatrix]
  let e : succStratum ≃ pairStratum :=
    { toFun := toPair
      invFun := ofPair
      left_inv := h_left
      right_inv := h_right }
  have hcard : Fintype.card succStratum = Fintype.card pairStratum := by
    exact Fintype.card_congr e
  simpa [succStratum] using hcard.trans hpair


theorem alternatingMatrix_oddRank_stratum_card_zero_succ_all_of_base_q2
    (n : ℕ)
    (hbase : ∀ r : ℕ,
      Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, B i i = 0) ∧
        (∀ i j : Fin n, B i j = B j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1} = 0) :
    ∀ r : ℕ,
      Fintype.card {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
        (∀ i : Fin (n + 1), A i i = 0) ∧
        (∀ i j : Fin (n + 1), A i j = A j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1} = 0 := by
  intro r
  exact alternatingMatrix_oddRank_stratum_card_zero_succ_of_base_q2 n r (hbase r) (by
    intro s _
    exact hbase s)




theorem alternatingMatrix_oddRank_stratum_card_zero_all_q2 :
    ∀ n r : ℕ,
      Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1} = 0 := by
  classical
    intro n
    induction n with
    | zero =>
        intro r
        have hEmpty : IsEmpty {A : Matrix (Fin 0) (Fin 0) (ZMod 2) //
            (∀ i : Fin 0, A i i = 0) ∧
            (∀ i j : Fin 0, A i j = A j i) ∧
            Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1} := by
          constructor
          intro A
          have hrank_le : Module.finrank (ZMod 2) (LinearMap.range ((A : Matrix (Fin 0) (Fin 0) (ZMod 2)).toLin')) ≤ 0 :=
            alternatingmatrix_tolinrank_range_finrank_le_q2 0 (A : Matrix (Fin 0) (Fin 0) (ZMod 2))
          have hrank_eq : Module.finrank (ZMod 2) (LinearMap.range ((A : Matrix (Fin 0) (Fin 0) (ZMod 2)).toLin')) = 2 * r + 1 :=
            A.property.2.2
          have hodd_le_zero : 2 * r + 1 ≤ 0 := by
            rw [hrank_eq] at hrank_le
            exact hrank_le
          omega
        letI : IsEmpty {A : Matrix (Fin 0) (Fin 0) (ZMod 2) //
            (∀ i : Fin 0, A i i = 0) ∧
            (∀ i j : Fin 0, A i j = A j i) ∧
            Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1} := hEmpty
        exact Fintype.card_eq_zero
    | succ n ih =>
        exact alternatingMatrix_oddRank_stratum_card_zero_succ_all_of_base_q2 n ih


theorem upperTriangular_canonical_oddRank_witness_false_q2
    (n r : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    (hodd :
      Module.finrank (ZMod 2)
        (LinearMap.range
          (Matrix.toLin'
            (((fun i j : Fin n =>
              if h : (i : ℕ) < (j : ℕ) then
                Q i ⟨j, h⟩
              else if h' : (j : ℕ) < (i : ℕ) then
                Q j ⟨i, h'⟩
              else
                0) : Matrix (Fin n) (Fin n) (ZMod 2))))) = 2 * r + 1) :
    False := by
  classical
    let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0
    have hvalid :
        (∀ i : Fin n, A i i = 0) ∧
          (∀ i j : Fin n, A i j = A j i) := by
      simpa [A] using upper_triangular_quadratic_coeff_to_alt_matrix_valid_q2 n Q
    have hArank :
        Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 1 := by
      simpa [A] using hodd
    let S : Type := ({B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 1})
    have hnonempty : Nonempty S := by
      exact ⟨⟨A, hvalid.1, hvalid.2, hArank⟩⟩
    have hzero : Fintype.card S = 0 := by
      simpa [S] using alternatingMatrix_oddRank_stratum_card_zero_all_q2 n r
    have hpos : 0 < Fintype.card S := by
      exact Fintype.card_pos_iff.mpr hnonempty
    rw [hzero] at hpos
    exact Nat.lt_irrefl 0 hpos


theorem upperTriangular_canonical_oddRankFiber_card_zero_q2
    (n r : ℕ) :
    (let Quad :=
      (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let toMatrix : Quad → Matrix (Fin n) (Fin n) (ZMod 2) := fun Q =>
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0);
     Fintype.card
       {Q : Quad //
         Module.finrank (ZMod 2)
           (LinearMap.range ((toMatrix Q).toLin')) = 2 * r + 1} = 0) := by
  classical
    dsimp only
    letI : IsEmpty
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) //
          Module.finrank (ZMod 2)
            (LinearMap.range
              (Matrix.toLin'
                (((fun i j : Fin n =>
                  if h : (i : ℕ) < (j : ℕ) then
                    Q i ⟨j, h⟩
                  else if h' : (j : ℕ) < (i : ℕ) then
                    Q j ⟨i, h'⟩
                  else
                    0) : Matrix (Fin n) (Fin n) (ZMod 2))))) = 2 * r + 1} :=
      ⟨fun Q => upperTriangular_canonical_oddRank_witness_false_q2 n r Q.1 Q.2⟩
    exact Fintype.card_eq_zero







theorem upper_triangular_reflected_rank_even_fin_q2
    (n : ℕ)
    (Q : (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) :
    (let toMatrix :
        ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
          Matrix (Fin n) (Fin n) (ZMod 2) := fun Q =>
        (fun i j : Fin n =>
          if h : (i : ℕ) < (j : ℕ) then
            Q i ⟨j, h⟩
          else if h' : (j : ℕ) < (i : ℕ) then
            Q j ⟨i, h'⟩
          else
            0);
      ∃ r : Fin (n + 1),
        Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) =
          2 * (r : ℕ)) := by
  classical
  dsimp
  let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2
  let A : Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun i j : Fin n =>
      if h : (i : ℕ) < (j : ℕ) then
        Q i ⟨j, h⟩
      else if h' : (j : ℕ) < (i : ℕ) then
        Q j ⟨i, h'⟩
      else
        0
  let M := Module.finrank (ZMod 2) (LinearMap.range (A.toLin'))
  have hle : M ≤ n := by
    simpa [M, A] using reflected_matrix_rank_le_card_q2 n Q
  have hEven : ∃ k : ℕ, M = 2 * k := by
    rcases Nat.even_or_odd M with h | h
    · rcases h with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    · rcases h with ⟨k, hkOdd⟩
      have hk : M = 2 * k + 1 := by
        omega
      have hcard_zero :
          Fintype.card {Q' : Quad //
            Module.finrank (ZMod 2)
              (LinearMap.range
                (Matrix.toLin'
                  (((fun i j : Fin n =>
                    if h : (i : ℕ) < (j : ℕ) then
                      Q' i ⟨j, h⟩
                    else if h' : (j : ℕ) < (i : ℕ) then
                      Q' j ⟨i, h'⟩
                    else
                      0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
              2 * k + 1} = 0 := by
        simpa [Quad] using upperTriangular_canonical_oddRankFiber_card_zero_q2 n k
      have hcard_pos :
          0 < Fintype.card {Q' : Quad //
            Module.finrank (ZMod 2)
              (LinearMap.range
                (Matrix.toLin'
                  (((fun i j : Fin n =>
                    if h : (i : ℕ) < (j : ℕ) then
                      Q' i ⟨j, h⟩
                    else if h' : (j : ℕ) < (i : ℕ) then
                      Q' j ⟨i, h'⟩
                    else
                      0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
              2 * k + 1} := by
        letI : Nonempty {Q' : Quad //
            Module.finrank (ZMod 2)
              (LinearMap.range
                (Matrix.toLin'
                  (((fun i j : Fin n =>
                    if h : (i : ℕ) < (j : ℕ) then
                      Q' i ⟨j, h⟩
                    else if h' : (j : ℕ) < (i : ℕ) then
                      Q' j ⟨i, h'⟩
                    else
                      0) : Matrix (Fin n) (Fin n) (ZMod 2))))) =
              2 * k + 1} :=
          ⟨⟨Q, by simpa [Quad, A, M] using hk⟩⟩
        exact Fintype.card_pos
      rw [hcard_zero] at hcard_pos
      exact (Nat.lt_irrefl 0 hcard_pos).elim
  rcases hEven with ⟨k, hk⟩
  exact ⟨⟨k, by omega⟩, by simpa [M, A] using hk⟩




theorem upper_triangular_nonzero_reflected_half_rank_exists_q2
    (n : ℕ) :
    ∃ halfRank :
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} →
        Fin (n + 1),
      ∀ Q :
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0},
        Module.finrank (ZMod 2)
          (LinearMap.range
            (Matrix.toLin'
              ((fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  Q.1 i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  Q.1 j ⟨i, h'⟩
                else
                  0) : Matrix (Fin n) (Fin n) (ZMod 2)))) =
          2 * (halfRank Q : ℕ) := by
  classical
    use fun Q => Classical.choose (upper_triangular_reflected_rank_even_fin_q2 n Q.1)
    intro Q
    simpa using Classical.choose_spec (upper_triangular_reflected_rank_even_fin_q2 n Q.1)


theorem upper_triangular_nonzero_balanced_affine_param_card_add_affine_eq_rank_weight_sum_add_affine_q2
    (n : ℕ) :
    (let Quad :=
      (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let AffineParam := (Fin n → ZMod 2) × ZMod 2;
     let toMatrix : Quad → Matrix (Fin n) (Fin n) (ZMod 2) := fun Q =>
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0);
     let BalancedAffineParam : Quad → AffineParam → Prop := fun Q b =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0)
        then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0;
     Fintype.card
       {p : {Q : Quad // Q ≠ 0} × AffineParam //
         BalancedAffineParam p.1.1 p.2}
       + 2 * (2 ^ n - 1)
      =
     (Finset.range (n + 1)).sum (fun r : ℕ =>
       Fintype.card
         {Q : {Q : Quad // Q ≠ 0} //
           Module.finrank (ZMod 2)
             (LinearMap.range ((toMatrix Q.1).toLin')) = 2 * r} *
         (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) +
       2 * (2 ^ n - 1)) := by
  classical
    rcases upper_triangular_nonzero_reflected_half_rank_exists_q2 n with ⟨halfRank, hhalf⟩
    exact Eq.trans
      (upper_triangular_nonzero_balanced_affine_param_card_add_affine_eq_halfrank_fiber_sum_q2
        n halfRank hhalf)
      (upper_triangular_nonzero_reflected_halfRank_weighted_sum_eq_rank_weight_sum_q2
        n halfRank hhalf)












theorem rank_fiber_zero_indicator_weight_eval_q2
    (n r : ℕ)
    (toMatrix :
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
        Matrix (Fin n) (Fin n) (ZMod 2))
    (hzero : toMatrix 0 = 0) :
    (let Quad :=
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
     let rankPred : Quad → Prop := fun Q =>
      Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r
     let weight : ℕ := 2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)
     (if rankPred 0 then weight else 0) =
       (if r = 0 then 2 * (2 ^ n - 1) else 0)) := by
  classical
  let Quad :=
    ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
  let rankPred : Quad → Prop := fun Q =>
    Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r
  let weight : ℕ := 2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)
  have hzeroLin : ((toMatrix (0 : Quad)).toLin') =
      (0 : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) := by
    rw [hzero]
    ext v i
    simp
  have hzeroRank : rankPred (0 : Quad) ↔ r = 0 := by
    constructor
    · intro h
      have hfin : Module.finrank (ZMod 2)
          (LinearMap.range (0 : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) = 0 := by
        simp
      have h' : (0 : ℕ) = 2 * r := by
        change Module.finrank (ZMod 2)
          (LinearMap.range ((toMatrix (0 : Quad)).toLin')) = 2 * r at h
        rw [hzeroLin] at h
        exact hfin.symm.trans h
      omega
    · intro hr
      subst r
      change Module.finrank (ZMod 2)
        (LinearMap.range ((toMatrix (0 : Quad)).toLin')) = 2 * 0
      rw [hzeroLin]
      simp
  change (if rankPred (0 : Quad) then weight else 0) =
    (if r = 0 then 2 * (2 ^ n - 1) else 0)
  by_cases hr : r = 0
  · subst r
    have hmem : rankPred (0 : Quad) := hzeroRank.mpr rfl
    simp [hmem, weight]
  · have hnot : ¬ rankPred (0 : Quad) := by
      intro h
      exact hr (hzeroRank.mp h)
    simp [hr, hnot]


theorem upperTriangular_rankWeight_summand_split_zero_q2
    (n r : ℕ)
    (toMatrix :
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
        Matrix (Fin n) (Fin n) (ZMod 2))
    (hzero : toMatrix 0 = 0) :
    Fintype.card
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) //
          Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))
      =
      Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q.1).toLin')) = 2 * r} *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)) +
        (if r = 0 then 2 * (2 ^ n - 1) else 0) := by
  classical
  let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2
  let rankPred : Quad → Prop := fun Q =>
    Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r
  let weight : ℕ := 2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)
  have hzeroWeight :
      (if rankPred 0 then weight else 0) =
        (if r = 0 then 2 * (2 ^ n - 1) else 0) := by
    simpa [Quad, rankPred, weight] using
      (rank_fiber_zero_indicator_weight_eval_q2 n r toMatrix hzero)
  have hsplit :
      Fintype.card {Q : Quad // rankPred Q} =
        Fintype.card {Q : {Q : Quad // Q ≠ 0} // rankPred Q.1} +
          (if rankPred 0 then 1 else 0) := by
    by_cases h0 : rankPred 0
    · let NonzeroFiber := {Q : {Q : Quad // Q ≠ 0} // rankPred Q.1}
      let e : {Q : Quad // rankPred Q} ≃ Option NonzeroFiber :=
        { toFun := fun Q =>
            if hQ : Q.1 = 0 then none else some ⟨⟨Q.1, hQ⟩, Q.2⟩
          invFun := fun o =>
            match o with
            | none => ⟨0, h0⟩
            | some Q => ⟨Q.1.1, Q.2⟩
          left_inv := by
            intro Q
            by_cases hQ : Q.1 = 0
            · apply Subtype.ext
              simp [hQ]
            · apply Subtype.ext
              simp [hQ]
          right_inv := by
            intro o
            cases o with
            | none => simp
            | some Q =>
                simp [Q.1.2] }
      have hcard :
          Fintype.card {Q : Quad // rankPred Q} = Fintype.card (Option NonzeroFiber) :=
        Fintype.card_congr e
      simpa [NonzeroFiber, h0] using hcard
    · let NonzeroFiber := {Q : {Q : Quad // Q ≠ 0} // rankPred Q.1}
      let e : {Q : Quad // rankPred Q} ≃ NonzeroFiber :=
        { toFun := fun Q =>
            ⟨⟨Q.1, by
                intro hQ
                exact h0 (by simpa [hQ] using Q.2)⟩, Q.2⟩
          invFun := fun Q => ⟨Q.1.1, Q.2⟩
          left_inv := by
            intro Q
            apply Subtype.ext
            rfl
          right_inv := by
            intro Q
            apply Subtype.ext
            apply Subtype.ext
            rfl }
      have hcard :
          Fintype.card {Q : Quad // rankPred Q} = Fintype.card NonzeroFiber :=
        Fintype.card_congr e
      simpa [NonzeroFiber, h0] using hcard
  have hmain :
      Fintype.card {Q : Quad // rankPred Q} * weight =
        Fintype.card {Q : {Q : Quad // Q ≠ 0} // rankPred Q.1} * weight +
          (if r = 0 then 2 * (2 ^ n - 1) else 0) := by
    calc
      Fintype.card {Q : Quad // rankPred Q} * weight
          = (Fintype.card {Q : {Q : Quad // Q ≠ 0} // rankPred Q.1} +
              (if rankPred 0 then 1 else 0)) * weight := by
            rw [hsplit]
      _ = Fintype.card {Q : {Q : Quad // Q ≠ 0} // rankPred Q.1} * weight +
            (if rankPred 0 then weight else 0) := by
            by_cases h0 : rankPred 0 <;> simp [h0, Nat.add_mul]
      _ = Fintype.card {Q : {Q : Quad // Q ≠ 0} // rankPred Q.1} * weight +
            (if r = 0 then 2 * (2 ^ n - 1) else 0) := by
            rw [hzeroWeight]
  simpa [Quad, rankPred, weight] using hmain




theorem zero_affine_indicator_sum_range_q2 (n : ℕ) :
    (Finset.range (n + 1)).sum (fun r : ℕ => if r = 0 then 2 * (2 ^ n - 1) else 0) =
      2 * (2 ^ n - 1) := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hne
    simp [hne]
  · intro hnot
    exact False.elim (hnot (by simp))


theorem upperTriangular_nonzero_rankWeight_sum_add_affine_eq_rankWeight_sum_q2
    (n : ℕ)
    (toMatrix :
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
        Matrix (Fin n) (Fin n) (ZMod 2))
    (hzero : toMatrix 0 = 0) :
    (Finset.range (n + 1)).sum (fun r : ℕ =>
        Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q.1).toLin')) = 2 * r} *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) +
      2 * (2 ^ n - 1)
    =
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      Fintype.card
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) //
          Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) := by
  classical
  rw [← zero_affine_indicator_sum_range_q2 n]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact (upperTriangular_rankWeight_summand_split_zero_q2 n r toMatrix hzero).symm












theorem alternating_matrix_rank_closed_product_tail_factorizations_q2
    (n r : ℕ) :
    ((Finset.range (2 * (r + 1))).prod
        (fun i : ℕ => 2 ^ ((n + 1) - i) - 1) =
      (2 ^ (n + 1) - 1) *
        ((Finset.range (2 * r)).prod
          (fun i : ℕ => 2 ^ (n - i) - 1)) *
        (2 ^ (n - 2 * r) - 1)) ∧
      ((Finset.range (2 * (r + 1))).prod
        (fun i : ℕ => 2 ^ (n - i) - 1) =
      ((Finset.range (2 * r)).prod
          (fun i : ℕ => 2 ^ (n - i) - 1)) *
        (2 ^ (n - 2 * r) - 1) *
        (2 ^ (n - (2 * r + 1)) - 1)) := by
  classical
  constructor
  · have hlen : 2 * (r + 1) = (2 * r + 1) + 1 := by omega
    calc
      (Finset.range (2 * (r + 1))).prod
          (fun i : ℕ => 2 ^ ((n + 1) - i) - 1)
          = (Finset.range ((2 * r + 1) + 1)).prod
              (fun i : ℕ => 2 ^ ((n + 1) - i) - 1) := by
              rw [hlen]
      _ = ((Finset.range (2 * r + 1)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) *
            (2 ^ (n + 1) - 1) := by
              rw [Finset.prod_range_succ']
              simp [Nat.succ_sub_succ_eq_sub]
      _ = (2 ^ (n + 1) - 1) *
            ((Finset.range (2 * r + 1)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) := by
              rw [mul_comm]
      _ = (2 ^ (n + 1) - 1) *
            (((Finset.range (2 * r)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) *
              (2 ^ (n - 2 * r) - 1)) := by
              rw [Finset.prod_range_succ]
      _ = (2 ^ (n + 1) - 1) *
            ((Finset.range (2 * r)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) *
            (2 ^ (n - 2 * r) - 1) := by
              rw [mul_assoc]
  · have hlen : 2 * (r + 1) = (2 * r + 1) + 1 := by omega
    calc
      (Finset.range (2 * (r + 1))).prod
          (fun i : ℕ => 2 ^ (n - i) - 1)
          = (Finset.range ((2 * r + 1) + 1)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1) := by
              rw [hlen]
      _ = ((Finset.range (2 * r + 1)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) *
            (2 ^ (n - (2 * r + 1)) - 1) := by
              rw [Finset.prod_range_succ]
      _ = (((Finset.range (2 * r)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) *
            (2 ^ (n - 2 * r) - 1)) *
            (2 ^ (n - (2 * r + 1)) - 1) := by
              rw [Finset.prod_range_succ]




theorem alternating_matrix_rank_closed_power_tail_identities_q2
    (n r : ℕ) (hvalid : 2 * r + 1 ≤ n) :
    (2 ^ (n + 1) - 1 =
      2 ^ (2 * r + 2) * (2 ^ (n - (2 * r + 1)) - 1) +
        (2 ^ (2 * r + 2) - 1)) ∧
      ((2 ^ n - 2 ^ (2 * r)) * 2 ^ (r * (r - 1)) =
        2 ^ ((r + 1) * r) * (2 ^ (n - 2 * r) - 1)) := by
  classical
  let a : ℕ := n - (2 * r + 1)
  have hn : n = 2 * r + 1 + a := by
    omega
  constructor
  · rw [hn]
    have hsub : 2 * r + 1 + a - (2 * r + 1) = a := by
      omega
    have hsum : 2 * r + 1 + a + 1 = 2 * r + 2 + a := by
      omega
    rw [hsub, hsum]
    have hpow : 2 ^ (2 * r + 2 + a) = 2 ^ (2 * r + 2) * 2 ^ a := by
      rw [pow_add]
    rw [hpow]
    rw [Nat.mul_sub_left_distrib]
    simp only [mul_one]
    have hBpos : 0 < 2 ^ (2 * r + 2) := by
      exact pow_pos (by norm_num : (0 : ℕ) < 2) _
    have hXpos : 0 < 2 ^ a := by
      exact pow_pos (by norm_num : (0 : ℕ) < 2) _
    have hBXle : 2 ^ (2 * r + 2) ≤ 2 ^ (2 * r + 2) * 2 ^ a := by
      have h1X : 1 ≤ 2 ^ a := Nat.succ_le_of_lt hXpos
      simpa using Nat.mul_le_mul_left (2 ^ (2 * r + 2)) h1X
    omega
  · rw [hn]
    have hsub : 2 * r + 1 + a - 2 * r = a + 1 := by
      omega
    have hsum : 2 * r + 1 + a = 2 * r + (a + 1) := by
      omega
    rw [hsub, hsum]
    have hpow : 2 ^ (2 * r + (a + 1)) = 2 ^ (2 * r) * 2 ^ (a + 1) := by
      rw [pow_add]
    rw [hpow]
    nth_rewrite 2 [← Nat.mul_one (2 ^ (2 * r))]
    rw [← Nat.mul_sub_left_distrib]
    have hexp : 2 * r + r * (r - 1) = (r + 1) * r := by
      cases r with
      | zero =>
          norm_num
      | succ k =>
          simp
          ring
    rw [mul_assoc]
    rw [mul_comm (2 ^ (a + 1) - 1) (2 ^ (r * (r - 1)))]
    rw [← mul_assoc]
    rw [← pow_add]
    rw [hexp]


theorem alternatingMatrix_rankClosed_numerator_recurrence_q2
    (n r : ℕ) (hvalid : 2 * r + 1 ≤ n) :
    (let num : ℕ → ℕ → ℕ := fun m s =>
      2 ^ (s * (s - 1)) *
        (Finset.range (2 * s)).prod (fun i : ℕ => 2 ^ (m - i) - 1);
    num (n + 1) (r + 1) =
      2 ^ (2 * r + 2) * num n (r + 1) +
        (2 ^ n - 2 ^ (2 * r)) * num n r * (2 ^ (2 * r + 2) - 1)) := by
  classical
    dsimp
    have hprod := alternating_matrix_rank_closed_product_tail_factorizations_q2 n r
    have hpow := alternating_matrix_rank_closed_power_tail_identities_q2 n r hvalid
    rw [hprod.1, hprod.2, hpow.1]
    have htail :
        (2 ^ n - 2 ^ (2 * r)) *
            (2 ^ (r * (r - 1)) *
              ((Finset.range (2 * r)).prod
                (fun i : ℕ => 2 ^ (n - i) - 1))) =
          (2 ^ ((r + 1) * r) * (2 ^ (n - 2 * r) - 1)) *
            ((Finset.range (2 * r)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) := by
      rw [← Nat.mul_assoc, hpow.2]
    rw [htail]
    simp only [add_mul, mul_add]
    ac_rfl








theorem alternatingMatrix_rankClosed_divisor_recurrence_q2
    (r : ℕ) :
    (let den : ℕ → ℕ := fun s =>
      (Finset.range s).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1);
    den (r + 1) = den r * (2 ^ (2 * r + 2) - 1)) := by
  simp [Finset.prod_range_succ, Nat.mul_add, Nat.add_comm]






theorem num_succ_exact_multiple_from_witnesses_q2
    (n r q_succ q_base : ℕ) (hvalid : 2 * r + 1 ≤ n) :
    (let num : ℕ → ℕ → ℕ := fun m s =>
      2 ^ (s * (s - 1)) *
        (Finset.range (2 * s)).prod (fun i : ℕ => 2 ^ (m - i) - 1);
     let den : ℕ → ℕ := fun s =>
      (Finset.range s).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1);
     num n (r + 1) = den (r + 1) * q_succ →
     num n r = den r * q_base →
     num (n + 1) (r + 1) =
       den (r + 1) *
         (2 ^ (2 * r + 2) * q_succ +
           (2 ^ n - 2 ^ (2 * r)) * q_base)) := by
  classical
  dsimp
  intro hsucc hbase
  have hnum := alternatingMatrix_rankClosed_numerator_recurrence_q2 n r hvalid
  have hden := alternatingMatrix_rankClosed_divisor_recurrence_q2 r
  dsimp at hnum hden
  rw [hnum, hsucc, hbase, hden]
  ring_nf




theorem den_mul_div_cancel_q2
    (s q : ℕ) :
    (let den : ℕ → ℕ := fun t =>
      (Finset.range t).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1);
     den s * q / den s = q) := by
  classical
    dsimp
    have hden_pos :
        0 <
          ((Finset.range s).prod
            (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) := by
      induction s with
      | zero =>
          simp
      | succ s ih =>
          rw [Finset.prod_range_succ]
          have hfac : 0 < 2 ^ (2 * (s + 1)) - 1 := by
            have hpow : 1 < 2 ^ (2 * (s + 1)) := by
              exact Nat.one_lt_pow (by omega : 2 * (s + 1) ≠ 0) (by norm_num : (1 : ℕ) < 2)
            omega
          exact Nat.mul_pos ih hfac
    simp [Nat.mul_comm]


theorem alternatingMatrix_rankClosed_quotient_recurrence_from_components_q2
    (n r : ℕ) (hvalid : 2 * r + 1 ≤ n)
    (hdiv_succ :
      ((Finset.range (r + 1)).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
        2 ^ ((r + 1) * r) *
          (Finset.range (2 * (r + 1))).prod (fun i : ℕ => 2 ^ (n - i) - 1))
    (hdiv_base :
      ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
        2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) :
    (let num : ℕ → ℕ → ℕ := fun m s =>
      2 ^ (s * (s - 1)) *
        (Finset.range (2 * s)).prod (fun i : ℕ => 2 ^ (m - i) - 1);
     let den : ℕ → ℕ := fun s =>
      (Finset.range s).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1);
     num (n + 1) (r + 1) / den (r + 1) =
      2 ^ (2 * r + 2) * (num n (r + 1) / den (r + 1)) +
        (2 ^ n - 2 ^ (2 * r)) * (num n r / den r)) := by
  classical
    rcases hdiv_succ with ⟨q_succ, hq_succ⟩
    rcases hdiv_base with ⟨q_base, hq_base⟩
    have hfact :=
      (num_succ_exact_multiple_from_witnesses_q2 n r q_succ q_base hvalid) hq_succ hq_base
    dsimp at hfact hq_succ hq_base ⊢
    rw [hfact, hq_succ, hq_base]
    rw [den_mul_div_cancel_q2 (r + 1) (2 ^ (2 * r + 2) * q_succ + (2 ^ n - 2 ^ (2 * r)) * q_base),
      den_mul_div_cancel_q2 (r + 1) q_succ,
      den_mul_div_cancel_q2 r q_base]
















theorem borderMatrix_rankFiber_card_of_base_tolinRank
    (n k : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = k) :
    (Fintype.card {v : Fin n → ZMod 2 //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              v ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              v ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k)}
      = 2 ^ k) ∧
    (Fintype.card {v : Fin n → ZMod 2 //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              v ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              v ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k + 2)}
      = 2 ^ n - 2 ^ k) := by
  classical
  let R : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range (B.toLin')
  let Pk : (Fin n → ZMod 2) → Prop := fun v => (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j => if hi : (i : ℕ) < n then if hj : (j : ℕ) < n then B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else v ⟨(i : ℕ), hi⟩ else if hj : (j : ℕ) < n then v ⟨(j : ℕ), hj⟩ else 0; Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k)
  let Pk2 : (Fin n → ZMod 2) → Prop := fun v => (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) := fun i j => if hi : (i : ℕ) < n then if hj : (j : ℕ) < n then B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else v ⟨(i : ℕ), hi⟩ else if hj : (j : ℕ) < n then v ⟨(j : ℕ), hj⟩ else 0; Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k + 2)
  have hPk : ∀ v : Fin n → ZMod 2, Pk v ↔ v ∈ R := by
    intro v
    constructor
    · intro hv
      by_contra hnot
      have hAv2 : Pk2 v := by
        have h := borderMatrix_toLinRank_eq_add_two_of_not_range_membership n B hdiag hsymm v (by simpa [R] using hnot)
        simpa [Pk2, hrank] using h
      have hEq : k = k + 2 := hv.symm.trans hAv2
      omega
    · intro hv
      have h := borderMatrix_toLinRank_eq_of_range_membership n B hdiag hsymm v (by simpa [R] using hv)
      simpa [Pk, hrank] using h
  have hPk2 : ∀ v : Fin n → ZMod 2, Pk2 v ↔ v ∉ R := by
    intro v
    constructor
    · intro hv
      by_contra hin
      have hAv : Pk v := by
        have h := borderMatrix_toLinRank_eq_of_range_membership n B hdiag hsymm v (by simpa [R] using hin)
        simpa [Pk, hrank] using h
      have hEq : k = k + 2 := hAv.symm.trans hv
      omega
    · intro hv
      have h := borderMatrix_toLinRank_eq_add_two_of_not_range_membership n B hdiag hsymm v (by simpa [R] using hv)
      simpa [Pk2, hrank] using h
  have hcardR : Fintype.card {v : Fin n → ZMod 2 // v ∈ R} = 2 ^ k := by
    have h1 : Fintype.card {v : Fin n → ZMod 2 // v ∈ R} = Fintype.card R := rfl
    rw [h1]
    simpa [R] using card_range_tolin_prime_eq_pow_finrank n k B hrank
  have htotal : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
    simp
  constructor
  · change Fintype.card {v : Fin n → ZMod 2 // Pk v} = 2 ^ k
    calc
      Fintype.card {v : Fin n → ZMod 2 // Pk v} = Fintype.card {v : Fin n → ZMod 2 // v ∈ R} := by
        exact Fintype.card_congr (Equiv.subtypeEquivRight hPk)
      _ = 2 ^ k := hcardR
  · change Fintype.card {v : Fin n → ZMod 2 // Pk2 v} = 2 ^ n - 2 ^ k
    have hcardNotR : Fintype.card {v : Fin n → ZMod 2 // v ∉ R} = 2 ^ n - 2 ^ k := by
      calc
        Fintype.card {v : Fin n → ZMod 2 // v ∉ R} = Fintype.card (Fin n → ZMod 2) - Fintype.card {v : Fin n → ZMod 2 // v ∈ R} := by
          simp
        _ = 2 ^ n - 2 ^ k := by
          rw [htotal, hcardR]
    calc
      Fintype.card {v : Fin n → ZMod 2 // Pk2 v} = Fintype.card {v : Fin n → ZMod 2 // v ∉ R} := by
        exact Fintype.card_congr (Equiv.subtypeEquivRight hPk2)
      _ = 2 ^ n - 2 ^ k := hcardNotR




theorem card_subtype_prod_eq_sum_fiber
    {α β : Type*} [Fintype α] [Fintype β]
    (P : α → β → Prop)
    [DecidablePred (fun p : α × β => P p.1 p.2)]
    [∀ a : α, DecidablePred (fun b : β => P a b)] :
    Fintype.card {p : α × β // P p.1 p.2}
      = (Finset.univ : Finset α).sum (fun a => Fintype.card {b : β // P a b}) := by
  classical
    let e : {p : α × β // P p.1 p.2} ≃ Sigma (fun a : α => {b : β // P a b}) :=
      { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
        invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
        left_inv := by
          intro p
          cases p with
          | mk p hp =>
            cases p
            rfl
        right_inv := by
          intro q
          cases q with
          | mk a b =>
            cases b
            rfl }
    calc
      Fintype.card {p : α × β // P p.1 p.2}
          = Fintype.card (Sigma (fun a : α => {b : β // P a b})) :=
        Fintype.card_congr e
      _ = (Finset.univ : Finset α).sum (fun a => Fintype.card {b : β // P a b}) := by
        simp


theorem alternatingMatrix_baseRank_borderRankFiber_sigma_card
    (n k : ℕ) :
    let base : Type := {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = k};
    (Fintype.card {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k)}
      = 2 ^ k * Fintype.card base) ∧
    (Fintype.card {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k + 2)}
      = (2 ^ n - 2 ^ k) * Fintype.card base) := by
  classical
  let base : Type := {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = k}
  change
    (Fintype.card {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k)}
      = 2 ^ k * Fintype.card base) ∧
    (Fintype.card {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k + 2)}
      = (2 ^ n - 2 ^ k) * Fintype.card base)
  constructor
  · rw [card_subtype_prod_eq_sum_fiber
        (α := base) (β := Fin n → ZMod 2)
        (P := fun b v =>
          (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
            fun i j =>
              if hi : (i : ℕ) < n then
                if hj : (j : ℕ) < n then
                  b.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
                else
                  v ⟨(i : ℕ), hi⟩
              else
                if hj : (j : ℕ) < n then
                  v ⟨(j : ℕ), hj⟩
                else
                  0;
           Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k))]
    trans (Finset.univ : Finset base).sum (fun _ : base => 2 ^ k)
    · apply Finset.sum_congr rfl
      intro b hb
      exact (borderMatrix_rankFiber_card_of_base_tolinRank n k b.1 b.2.1 b.2.2.1 b.2.2.2).1
    · simp [Finset.card_univ, Nat.mul_comm]
  · rw [card_subtype_prod_eq_sum_fiber
        (α := base) (β := Fin n → ZMod 2)
        (P := fun b v =>
          (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
            fun i j =>
              if hi : (i : ℕ) < n then
                if hj : (j : ℕ) < n then
                  b.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
                else
                  v ⟨(i : ℕ), hi⟩
              else
                if hj : (j : ℕ) < n then
                  v ⟨(j : ℕ), hj⟩
                else
                  0;
           Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = k + 2))]
    trans (Finset.univ : Finset base).sum (fun _ : base => 2 ^ n - 2 ^ k)
    · apply Finset.sum_congr rfl
      intro b hb
      exact (borderMatrix_rankFiber_card_of_base_tolinRank n k b.1 b.2.1 b.2.2.1 b.2.2.2).2
    · simp [Finset.card_univ, Nat.mul_comm]




theorem border_rank_target_iff_base_rank_membership
    (n r : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hdiag : ∀ i : Fin n, B i i = 0)
    (hsymm : ∀ i j : Fin n, B i j = B j i)
    (v : Fin n → ZMod 2) :
    (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              B ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              v ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              v ⟨(j : ℕ), hj⟩
            else
              0;
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 2)
      ↔
      (Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2 ∧
          v ∈ LinearMap.range (B.toLin')) ∨
        (Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r ∧
          v ∉ LinearMap.range (B.toLin')) := by
  classical
  dsimp only
  by_cases hv : v ∈ LinearMap.range (B.toLin')
  · have hrank := borderMatrix_toLinRank_eq_of_range_membership n B hdiag hsymm v hv
    rw [hrank]
    simp [hv]
  · have hrank := borderMatrix_toLinRank_eq_add_two_of_not_range_membership n B hdiag hsymm v hv
    rw [hrank]
    simp [hv]


theorem alternatingMatrix_borderPair_toLinRank_stratum_card_recurrence_succ_q2
    (n r : ℕ) :
    let base : Type := {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i)};
    Fintype.card {p : base × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 2)}
      =
      2 ^ (2 * r + 2) *
        Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2}
      +
      (2 ^ n - 2 ^ (2 * r)) *
        Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r} := by
  classical
    let base0 : Type := {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i)}
    let baseHi : Type := {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2}
    let baseLo : Type := {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r}
    let T : Type := {p : base0 × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 2)}
    let T_hi : Type := {p : baseHi × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 2)}
    let T_lo : Type := {p : baseLo × (Fin n → ZMod 2) //
      (let A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
        fun i j =>
          if hi : (i : ℕ) < n then
            if hj : (j : ℕ) < n then
              p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
            else
              p.2 ⟨(i : ℕ), hi⟩
          else
            if hj : (j : ℕ) < n then
              p.2 ⟨(j : ℕ), hj⟩
            else
              0;
       Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 2)}
    have hpart : Fintype.card T = Fintype.card T_hi + Fintype.card T_lo := by
      let e : T ≃ T_hi ⊕ T_lo :=
        { toFun := fun x =>
            by
              rcases x with ⟨⟨⟨B, hB⟩, v⟩, hx⟩
              by_cases hrank :
                  Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2
              · exact Sum.inl ⟨(⟨B, ⟨hB.1, hB.2, hrank⟩⟩, v), hx⟩
              · have hlow :
                    Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r := by
                  have hcases :=
                    (border_rank_target_iff_base_rank_membership n r B hB.1 hB.2 v).mp hx
                  cases hcases with
                  | inl h =>
                      exact False.elim (hrank h.1)
                  | inr h =>
                      exact h.1
                exact Sum.inr ⟨(⟨B, ⟨hB.1, hB.2, hlow⟩⟩, v), hx⟩
          invFun := fun y =>
            by
              cases y with
              | inl y =>
                  rcases y with ⟨⟨⟨B, hB⟩, v⟩, hy⟩
                  exact ⟨(⟨B, ⟨hB.1, hB.2.1⟩⟩, v), hy⟩
              | inr y =>
                  rcases y with ⟨⟨⟨B, hB⟩, v⟩, hy⟩
                  exact ⟨(⟨B, ⟨hB.1, hB.2.1⟩⟩, v), hy⟩
          left_inv := by
            intro x
            rcases x with ⟨⟨⟨B, hB⟩, v⟩, hx⟩
            dsimp
            by_cases hrank :
                Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2
            · rw [dif_pos hrank]
            · rw [dif_neg hrank]
          right_inv := by
            intro y
            cases y with
            | inl y =>
                rcases y with ⟨⟨⟨B, hB⟩, v⟩, hy⟩
                dsimp
                have hrank :
                    Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2 :=
                  hB.2.2
                rw [dif_pos hrank]
            | inr y =>
                rcases y with ⟨⟨⟨B, hB⟩, v⟩, hy⟩
                dsimp
                have hnot :
                    ¬ Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2 := by
                  intro hrank
                  have heq : 2 * r = 2 * r + 2 := hB.2.2.symm.trans hrank
                  exact (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide : 0 < 2))) heq
                rw [dif_neg hnot] }
      simpa using (Fintype.card_congr e)
    have hhi :
        Fintype.card T_hi = 2 ^ (2 * r + 2) * Fintype.card baseHi := by
      exact (alternatingMatrix_baseRank_borderRankFiber_sigma_card n (2 * r + 2)).1
    have hlo :
        Fintype.card T_lo = (2 ^ n - 2 ^ (2 * r)) * Fintype.card baseLo := by
      exact (alternatingMatrix_baseRank_borderRankFiber_sigma_card n (2 * r)).2
    have hmain :
        Fintype.card T =
          2 ^ (2 * r + 2) * Fintype.card baseHi +
            (2 ^ n - 2 ^ (2 * r)) * Fintype.card baseLo := by
      calc
        Fintype.card T = Fintype.card T_hi + Fintype.card T_lo := hpart
        _ =
            2 ^ (2 * r + 2) * Fintype.card baseHi +
              (2 ^ n - 2 ^ (2 * r)) * Fintype.card baseLo := by
          rw [hhi, hlo]
    change Fintype.card T =
        2 ^ (2 * r + 2) * Fintype.card baseHi +
          (2 ^ n - 2 ^ (2 * r)) * Fintype.card baseLo
    exact hmain













theorem succ_rank_stratum_card_transport_of_equiv
    (n r : ℕ) (border : Type) [Fintype border]
    (e :
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
        (∀ i : Fin (n + 1), A i i = 0) ∧
        (∀ i j : Fin (n + 1), A i j = A j i)} ≃ border) :
    Fintype.card {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
      (∀ i : Fin (n + 1), A i i = 0) ∧
      (∀ i j : Fin (n + 1), A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 2}
      =
    Fintype.card {p : border //
      Module.finrank (ZMod 2) (LinearMap.range (((e.symm p).val).toLin')) = 2 * r + 2} := by
  classical
    exact Fintype.card_congr
      { toFun := fun A =>
          ⟨e ⟨A.val, A.property.1, A.property.2.1⟩, by
            rw [e.symm_apply_apply ⟨A.val, A.property.1, A.property.2.1⟩]
            exact A.property.2.2⟩
        invFun := fun p =>
          ⟨(e.symm p.val).val, (e.symm p.val).property.1,
            (e.symm p.val).property.2, p.property⟩
        left_inv := by
          intro A
          exact Subtype.ext
            (congrArg
              (fun B :
                  {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
                    (∀ i : Fin (n + 1), M i i = 0) ∧
                    (∀ i j : Fin (n + 1), M i j = M j i)} =>
                B.val)
              (e.symm_apply_apply ⟨A.val, A.property.1, A.property.2.1⟩))
        right_inv := by
          intro p
          apply Subtype.ext
          simp }


theorem alternatingMatrix_toLinRank_stratum_card_recurrence_succ_q2
    (n r : ℕ) :
    Fintype.card {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
      (∀ i : Fin (n + 1), A i i = 0) ∧
      (∀ i j : Fin (n + 1), A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r + 2}
      =
      2 ^ (2 * r + 2) *
        Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r + 2}
      + (2 ^ n - 2 ^ (2 * r)) *
        Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, B i i = 0) ∧
          (∀ i j : Fin n, B i j = B j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r} := by
  classical
    let base : Type := {B : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, B i i = 0) ∧
      (∀ i j : Fin n, B i j = B j i)}
    let succBase : Type := {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
      (∀ i : Fin (n + 1), A i i = 0) ∧
      (∀ i j : Fin (n + 1), A i j = A j i)}
    let borderMatrix : base × (Fin n → ZMod 2) →
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) :=
      fun p i j =>
        if hi : (i : ℕ) < n then
          if hj : (j : ℕ) < n then
            p.1.1 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩
          else
            p.2 ⟨(i : ℕ), hi⟩
        else
          if hj : (j : ℕ) < n then
            p.2 ⟨(j : ℕ), hj⟩
          else
            0
    have hBorderAlt :
        ∀ p : base × (Fin n → ZMod 2),
          (∀ i : Fin (n + 1), borderMatrix p i i = 0) ∧
            (∀ i j : Fin (n + 1), borderMatrix p i j = borderMatrix p j i) := by
      intro p
      constructor
      · intro i
        by_cases hi : (i : ℕ) < n
        · simp [borderMatrix, hi, p.1.2.1 ⟨(i : ℕ), hi⟩]
        · simp [borderMatrix, hi]
      · intro i j
        by_cases hi : (i : ℕ) < n
        · by_cases hj : (j : ℕ) < n
          · simpa [borderMatrix, hi, hj] using
              (p.1.2.2 ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩)
          · simp [borderMatrix, hi, hj]
        · by_cases hj : (j : ℕ) < n
          · simp [borderMatrix, hi, hj]
          · simp [borderMatrix, hi, hj]
    let toBorder : succBase → base × (Fin n → ZMod 2) :=
      fun A =>
        (⟨fun i j => A.1 (Fin.castSucc i) (Fin.castSucc j),
            by
              constructor
              · intro i
                exact A.2.1 (Fin.castSucc i)
              · intro i j
                exact A.2.2 (Fin.castSucc i) (Fin.castSucc j)⟩,
          fun i => A.1 (Fin.castSucc i) (Fin.last n))
    let ofBorder : base × (Fin n → ZMod 2) → succBase :=
      fun p => ⟨borderMatrix p, hBorderAlt p⟩
    have hleft : Function.LeftInverse ofBorder toBorder := by
      intro A
      apply Subtype.ext
      funext i j
      by_cases hi : (i : ℕ) < n
      · have hicut :
            (Fin.castSucc (⟨(i : ℕ), hi⟩ : Fin n) : Fin (n + 1)) = i := by
          apply Fin.ext
          rfl
        by_cases hj : (j : ℕ) < n
        · have hjcut :
              (Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n) : Fin (n + 1)) = j := by
            apply Fin.ext
            rfl
          simp [toBorder, ofBorder, borderMatrix, hi, hj, hicut, hjcut]
        · have hjlast : j = Fin.last n := by
            apply Fin.ext
            apply le_antisymm
            · exact Nat.le_of_lt_succ j.2
            · exact le_of_not_gt hj
          simp [toBorder, ofBorder, borderMatrix, hi, hicut, hjlast]
      · have hilast : i = Fin.last n := by
          apply Fin.ext
          apply le_antisymm
          · exact Nat.le_of_lt_succ i.2
          · exact le_of_not_gt hi
        by_cases hj : (j : ℕ) < n
        · have hjcut :
              (Fin.castSucc (⟨(j : ℕ), hj⟩ : Fin n) : Fin (n + 1)) = j := by
            apply Fin.ext
            rfl
          simp [toBorder, ofBorder, borderMatrix, hj, hilast, hjcut,
            A.2.2 j (Fin.last n)]
        · have hjlast : j = Fin.last n := by
            apply Fin.ext
            apply le_antisymm
            · exact Nat.le_of_lt_succ j.2
            · exact le_of_not_gt hj
          simp [toBorder, ofBorder, borderMatrix, hilast, hjlast,
            A.2.1 (Fin.last n)]
    have hright : Function.RightInverse ofBorder toBorder := by
      intro p
      cases p with
      | mk B v =>
        apply Prod.ext
        · apply Subtype.ext
          funext i j
          simp [toBorder, ofBorder, borderMatrix]
        · funext i
          simp [toBorder, ofBorder, borderMatrix]
    let e : succBase ≃ base × (Fin n → ZMod 2) :=
      { toFun := toBorder
        invFun := ofBorder
        left_inv := hleft
        right_inv := hright }
    rw [succ_rank_stratum_card_transport_of_equiv n r (base × (Fin n → ZMod 2)) e]
    simpa [e, ofBorder, borderMatrix, base, succBase] using
      (alternatingMatrix_borderPair_toLinRank_stratum_card_recurrence_succ_q2 n r)




theorem alternatingmatrix_tolinrank_invalid_zero_facts_q2
    (n r : ℕ) (h : n < 2 * r) :
    (Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r} = 0) ∧
    (((2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
        ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) = 0) := by
  classical
  constructor
  ·
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun A => by
      have hle := alternatingmatrix_tolinrank_range_finrank_le_q2 n A.1
      have hlt : n < Module.finrank (ZMod 2) (LinearMap.range (A.1.toLin')) := by
        simpa [A.2.2.2] using h
      exact (not_lt_of_ge hle hlt).elim⟩
  ·
    have hnmem : n ∈ Finset.range (2 * r) := Finset.mem_range.mpr h
    have hprod :
        (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1) = 0 := by
      exact Finset.prod_eq_zero hnmem (by simp)
    simp [hprod]




theorem alternating_matrix_rank_zero_stratum_card_q2
    (n : ℕ) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 0} = 1 := by
  classical
    apply Fintype.card_eq_one_iff.mpr
    use ⟨0, by
      constructor
      · intro i
        simp
      · constructor
        · intro i j
          simp
        · simp⟩
    intro A
    apply Subtype.ext
    ext i j
    have hrank :
        Module.finrank (ZMod 2) (LinearMap.range (A.val.toLin')) = 0 :=
      A.property.2.2
    have hmem :
        A.val.toLin' (Pi.single j (1 : ZMod 2)) ∈ LinearMap.range (A.val.toLin') :=
      LinearMap.mem_range_self A.val.toLin' (Pi.single j (1 : ZMod 2))
    have hsubzero :
        (⟨A.val.toLin' (Pi.single j (1 : ZMod 2)), hmem⟩ :
          LinearMap.range (A.val.toLin')) = 0 := by
      by_contra hne
      haveI : Nontrivial (LinearMap.range (A.val.toLin')) :=
        ⟨⟨
          (⟨A.val.toLin' (Pi.single j (1 : ZMod 2)), hmem⟩ :
            LinearMap.range (A.val.toLin')),
          0,
          hne⟩⟩
      have hpos :
          0 < Module.finrank (ZMod 2) (LinearMap.range (A.val.toLin')) := by
        exact Module.finrank_pos
      rw [hrank] at hpos
      exact Nat.lt_irrefl 0 hpos
    have hzero :
        A.val.toLin' (Pi.single j (1 : ZMod 2)) = 0 := by
      simpa using congrArg Subtype.val hsubzero
    have hcoord :
        (A.val.toLin' (Pi.single j (1 : ZMod 2))) i = 0 := by
      exact congr_fun hzero i
    change (A.val.mulVec (Pi.single j (1 : ZMod 2))) i = 0 at hcoord
    simpa [Matrix.mulVec] using hcoord








theorem alternating_matrix_rank_closed_numerator_recurrence_expanded_q2
    (n r : ℕ) (hvalid : 2 * r + 1 ≤ n) :
    2 ^ ((r + 1) * r) *
        (Finset.range (2 * (r + 1))).prod
          (fun i : ℕ => 2 ^ ((n + 1) - i) - 1)
      =
      2 ^ (2 * r + 2) *
          (2 ^ ((r + 1) * r) *
            (Finset.range (2 * (r + 1))).prod
              (fun i : ℕ => 2 ^ (n - i) - 1))
        +
        (2 ^ (2 * r + 2) - 1) * (2 ^ n - 2 ^ (2 * r)) *
          (2 ^ (r * (r - 1)) *
            (Finset.range (2 * r)).prod
              (fun i : ℕ => 2 ^ (n - i) - 1)) := by
  simpa [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    (alternatingMatrix_rankClosed_numerator_recurrence_q2 n r hvalid)




theorem den_dvd_linear_combination_q2
    (r A B C E : ℕ)
    (hA :
      ((Finset.range (r + 1)).prod
        (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣ A)
    (hB :
      ((Finset.range r).prod
        (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣ B) :
    ((Finset.range (r + 1)).prod
      (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
      C * A + (2 ^ (2 * (r + 1)) - 1) * E * B := by
  classical
    apply dvd_add
    · exact dvd_mul_of_dvd_right hA C
    · rcases hB with ⟨k, hk⟩
      use E * k
      rw [show
        ((Finset.range (r + 1)).prod
          (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) =
          ((Finset.range r).prod
            (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) *
            (2 ^ (2 * (r + 1)) - 1) by
        simpa using
          (Finset.prod_range_succ
            (f := fun i : ℕ => 2 ^ (2 * (i + 1)) - 1) r)]
      rw [hk]
      ac_rfl


theorem alternatingMatrix_rankClosed_den_dvd_num_succ_from_witnesses_q2
    (n r : ℕ) (hvalid : 2 * r + 1 ≤ n)
    (hdiv_succ :
      ((Finset.range (r + 1)).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
        2 ^ ((r + 1) * r) *
          (Finset.range (2 * (r + 1))).prod (fun i : ℕ => 2 ^ (n - i) - 1))
    (hdiv_base :
      ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
        2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) :
    ((Finset.range (r + 1)).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
      2 ^ ((r + 1) * r) *
        (Finset.range (2 * (r + 1))).prod (fun i : ℕ => 2 ^ ((n + 1) - i) - 1) := by
  have hpow : 2 * (r + 1) = 2 * r + 2 := by
    ring
  have hfac : 2 ^ (2 * (r + 1)) - 1 = 2 ^ (2 * r + 2) - 1 := by
    rw [hpow]
  have hlin := by
    exact
      (den_dvd_linear_combination_q2 r
        (2 ^ ((r + 1) * r) *
          (Finset.range (2 * (r + 1))).prod (fun i : ℕ => 2 ^ (n - i) - 1))
        (2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1))
        (2 ^ (2 * r + 2))
        (2 ^ n - 2 ^ (2 * r))
        hdiv_succ hdiv_base)
  rw [hfac] at hlin
  have hrec :=
    alternating_matrix_rank_closed_numerator_recurrence_expanded_q2 n r hvalid
  exact hrec.symm ▸ (by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlin)




theorem alternatingmatrix_rankclosed_num_prod_zero_of_lt_two_mul_q2
    (n r : ℕ) (h : n < 2 * r) :
    (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1) = 0 := by
  classical
  apply Finset.prod_eq_zero
  · exact Finset.mem_range.mpr h
  · simp


theorem alternatingMatrix_rankClosed_den_dvd_num_q2
    (n r : ℕ) :
    ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
      2 ^ (r * (r - 1)) *
        (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1) := by
  classical
    revert r
    induction' n using Nat.strong_induction_on with n ih
    intro r
    by_cases hsmall : n < 2 * r
    · have hprod := alternatingmatrix_rankclosed_num_prod_zero_of_lt_two_mul_q2 n r hsmall
      rw [hprod, mul_zero]
      exact Nat.dvd_zero _
    · cases r with
      | zero =>
          simp
      | succ r =>
          cases n with
          | zero =>
              omega
          | succ n =>
              have hvalid : 2 * r + 1 ≤ n := by
                have hle : 2 * (r + 1) ≤ n + 1 := Nat.le_of_not_gt hsmall
                omega
              exact alternatingMatrix_rankClosed_den_dvd_num_succ_from_witnesses_q2 n r hvalid
                (ih n (Nat.lt_succ_self n) (r + 1))
                (ih n (Nat.lt_succ_self n) r)


theorem alternatingMatrix_toLinRank_stratum_card_closed_q2
    (n r : ℕ) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r}
      =
      (2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
        ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) := by
  classical
  induction n generalizing r with
  | zero =>
      cases r with
      | zero =>
          simpa using alternating_matrix_rank_zero_stratum_card_q2 0
      | succ r =>
          have hlt : 0 < 2 * (r + 1) := by
            omega
          have hz := alternatingmatrix_tolinrank_invalid_zero_facts_q2 0 (r + 1) hlt
          rw [hz.1, hz.2]
  | succ n ih =>
      cases r with
      | zero =>
          simpa using alternating_matrix_rank_zero_stratum_card_q2 (n + 1)
      | succ r =>
          by_cases hvalid : 2 * r + 1 ≤ n
          · have hrec' :
              Fintype.card {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2) //
                (∀ i : Fin (n + 1), A i i = 0) ∧
                (∀ i j : Fin (n + 1), A i j = A j i) ∧
                Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * (r + 1)}
                =
                2 ^ (2 * r + 2) *
                  Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
                    (∀ i : Fin n, B i i = 0) ∧
                    (∀ i j : Fin n, B i j = B j i) ∧
                    Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * (r + 1)}
                + (2 ^ n - 2 ^ (2 * r)) *
                  Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
                    (∀ i : Fin n, B i i = 0) ∧
                    (∀ i j : Fin n, B i j = B j i) ∧
                    Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * r} := by
              simpa [Nat.mul_add] using
                alternatingMatrix_toLinRank_stratum_card_recurrence_succ_q2 n r
            have hihSucc' :
              Fintype.card {B : Matrix (Fin n) (Fin n) (ZMod 2) //
                (∀ i : Fin n, B i i = 0) ∧
                (∀ i j : Fin n, B i j = B j i) ∧
                Module.finrank (ZMod 2) (LinearMap.range (B.toLin')) = 2 * (r + 1)}
                =
                (2 ^ ((r + 1) * r) *
                    (Finset.range (2 * (r + 1))).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
                  ((Finset.range (r + 1)).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) := by
              simpa [Nat.add_sub_cancel] using ih (r + 1)
            have hihBase := ih r
            have hdivSucc :
                ((Finset.range (r + 1)).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
                  2 ^ ((r + 1) * r) *
                    (Finset.range (2 * (r + 1))).prod (fun i : ℕ => 2 ^ (n - i) - 1) := by
              simpa [Nat.add_sub_cancel] using
                alternatingMatrix_rankClosed_den_dvd_num_q2 n (r + 1)
            have hdivBase :
                ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1)) ∣
                  2 ^ (r * (r - 1)) *
                    (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1) := by
              simpa using alternatingMatrix_rankClosed_den_dvd_num_q2 n r
            have hq :=
              alternatingMatrix_rankClosed_quotient_recurrence_from_components_q2
                n r hvalid hdivSucc hdivBase
            rw [hrec']
            rw [hihSucc', hihBase]
            simpa [Nat.add_sub_cancel] using hq.symm
          · have hlt : n + 1 < 2 * (r + 1) := by
              omega
            have hz := alternatingmatrix_tolinrank_invalid_zero_facts_q2 (n + 1) (r + 1) hlt
            rw [hz.1, hz.2]


theorem alternatingMatrix_rankClosed_balancedWeightTerm_q2
    (n r : ℕ) :
    Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))
      =
      ((2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
        ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)) := by
  rw [alternatingMatrix_toLinRank_stratum_card_closed_q2 n r]


theorem alternatingMatrix_rankClosed_balancedWeightSum_instantiated_q2
    (n : ℕ) :
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      Fintype.card {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)))
      =
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      ((2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
        ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) := by
  exact Finset.sum_congr rfl (fun r hr => alternatingMatrix_rankClosed_balancedWeightTerm_q2 n r)






theorem upper_triangular_coeff_actual_rank_fiber_card_eq_alternating_rank_stratum_q2
    (n r : ℕ)
    (toMatrix :
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
        Matrix (Fin n) (Fin n) (ZMod 2))
    (htoMatrix :
      ∀ Q,
        (∀ i : Fin n, toMatrix Q i i = 0) ∧
        (∀ i j : Fin n, toMatrix Q i j = toMatrix Q j i))
    (hbij : Function.Bijective
      (fun Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) =>
        (⟨toMatrix Q, htoMatrix Q⟩ :
          {A : Matrix (Fin n) (Fin n) (ZMod 2) //
            (∀ i : Fin n, A i i = 0) ∧
            (∀ i j : Fin n, A i j = A j i)}))) :
    Fintype.card
      {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) //
        Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r}
      =
    Fintype.card
      {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i) ∧
        Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r} := by
  classical
    let Quad := ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2)
    let Alt := {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i)}
    let α := {Q : Quad //
      Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r}
    let β := {A : Matrix (Fin n) (Fin n) (ZMod 2) //
      (∀ i : Fin n, A i i = 0) ∧
      (∀ i j : Fin n, A i j = A j i) ∧
      Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r}
    let g : α → β := fun Q =>
      ⟨toMatrix Q.1, by
        exact And.intro (htoMatrix Q.1).1 (And.intro (htoMatrix Q.1).2 Q.2)⟩
    have hg_inj : Function.Injective g := by
      intro Q1 Q2 h
      have hval : toMatrix Q1.1 = toMatrix Q2.1 := by
        exact congrArg (fun B : β => B.1) h
      have hAlt : (⟨toMatrix Q1.1, htoMatrix Q1.1⟩ : Alt) =
          (⟨toMatrix Q2.1, htoMatrix Q2.1⟩ : Alt) := by
        apply Subtype.ext
        exact hval
      have hbase : Q1.1 = Q2.1 := hbij.1 hAlt
      exact Subtype.ext hbase
    have hg_surj : Function.Surjective g := by
      intro B
      rcases hbij.2 (⟨B.1, And.intro B.2.1 B.2.2.1⟩ : Alt) with ⟨Q, hQ⟩
      have hmat : toMatrix Q = B.1 := by
        exact congrArg (fun A : Alt => A.1) hQ
      have hrank :
          Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r := by
        rw [hmat]
        exact B.2.2.2
      exact ⟨(⟨Q, hrank⟩ : α), by
        apply Subtype.ext
        exact hmat⟩
    change Fintype.card α = Fintype.card β
    exact Fintype.card_congr (Equiv.ofBijective g (And.intro hg_inj hg_surj))


theorem upperTriangularCoeff_rankFiber_weighted_sum_eq_alternatingRankStratum_q2
    (n : ℕ)
    (toMatrix :
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
        Matrix (Fin n) (Fin n) (ZMod 2))
    (htoMatrix :
      ∀ Q,
        (∀ i : Fin n, toMatrix Q i i = 0) ∧
        (∀ i j : Fin n, toMatrix Q i j = toMatrix Q j i))
    (hbij : Function.Bijective
      (fun Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) =>
        (⟨toMatrix Q, htoMatrix Q⟩ :
          {A : Matrix (Fin n) (Fin n) (ZMod 2) //
            (∀ i : Fin n, A i i = 0) ∧
            (∀ i j : Fin n, A i j = A j i)}))) :
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      Fintype.card
        {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) //
          Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)))
      =
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      Fintype.card
        {A : Matrix (Fin n) (Fin n) (ZMod 2) //
          (∀ i : Fin n, A i i = 0) ∧
          (∀ i j : Fin n, A i j = A j i) ∧
          Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r} *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) := by
  classical
    exact Finset.sum_congr rfl (by
      intro r hr
      rw [upper_triangular_coeff_actual_rank_fiber_card_eq_alternating_rank_stratum_q2 n r toMatrix htoMatrix hbij])




theorem upper_triangular_rank_weight_sum_closed_q2
    (n : ℕ)
    (toMatrix :
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
        Matrix (Fin n) (Fin n) (ZMod 2))
    (htoMatrix :
      ∀ Q,
        (∀ i : Fin n, toMatrix Q i i = 0) ∧
        (∀ i j : Fin n, toMatrix Q i j = toMatrix Q j i))
    (hbij : Function.Bijective
      (fun Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) =>
        (⟨toMatrix Q, htoMatrix Q⟩ :
          {A : Matrix (Fin n) (Fin n) (ZMod 2) //
            (∀ i : Fin n, A i i = 0) ∧
            (∀ i j : Fin n, A i j = A j i)}))) :
    (Finset.range (n + 1)).sum (fun r : ℕ =>
        Fintype.card
          {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) //
            Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q).toLin')) = 2 * r} *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)))
      =
      (Finset.range (n + 1)).sum (fun r : ℕ =>
        Fintype.card
          {A : Matrix (Fin n) (Fin n) (ZMod 2) //
            ((∀ i : Fin n, A i i = 0) ∧
              (∀ i j : Fin n, A i j = A j i)) ∧
            Module.finrank (ZMod 2) (LinearMap.range (A.toLin')) = 2 * r} *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) := by
  classical
  simpa [and_assoc] using
    (upperTriangularCoeff_rankFiber_weighted_sum_eq_alternatingRankStratum_q2 n toMatrix htoMatrix hbij)


theorem upperTriangular_nonzero_rankWeight_sum_add_affine_eq_closed_q2
    (n : ℕ)
    (toMatrix :
      ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
        Matrix (Fin n) (Fin n) (ZMod 2))
    (htoMatrix :
      ∀ Q,
        (∀ i : Fin n, toMatrix Q i i = 0) ∧
        (∀ i j : Fin n, toMatrix Q i j = toMatrix Q j i))
    (hzero : toMatrix 0 = 0)
    (hbij : Function.Bijective
      (fun Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) =>
        (⟨toMatrix Q, htoMatrix Q⟩ :
          {A : Matrix (Fin n) (Fin n) (ZMod 2) //
            (∀ i : Fin n, A i i = 0) ∧
            (∀ i j : Fin n, A i j = A j i)}))) :
    (Finset.range (n + 1)).sum (fun r : ℕ =>
        Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            Module.finrank (ZMod 2) (LinearMap.range ((toMatrix Q.1).toLin')) = 2 * r} *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) +
      2 * (2 ^ n - 1)
    =
    (Finset.range (n + 1)).sum (fun r : ℕ =>
      ((2 ^ (r * (r - 1)) *
          (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
        ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) := by
  exact
      (upperTriangular_nonzero_rankWeight_sum_add_affine_eq_rankWeight_sum_q2 n toMatrix hzero).trans
        ((upper_triangular_rank_weight_sum_closed_q2 n toMatrix htoMatrix hbij).trans
          (by
            simpa [and_assoc] using
              (alternatingMatrix_rankClosed_balancedWeightSum_instantiated_q2 n)))






theorem upper_triangular_quadratic_coeff_to_alt_matrix_injective_q2 (n : ℕ) :
    Function.Injective
      (fun Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) =>
        ((fun i j : Fin n =>
          if h : (i : ℕ) < (j : ℕ) then
            Q i ⟨j, h⟩
          else if h' : (j : ℕ) < (i : ℕ) then
            Q j ⟨i, h'⟩
          else
            0) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
  classical
  intro Q R hQR
  funext i j
  exact by
    have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => A i j.1) hQR
    simpa [j.2] using hentry


theorem upper_triangular_quadratic_coeff_to_alt_matrix_bijective_q2
    (n : ℕ) :
    (let Quad :=
      (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let AltMat :=
      {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i)};
     let toMatrix : Quad → Matrix (Fin n) (Fin n) (ZMod 2) := fun Q =>
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0);
     ∃ htoMatrix :
        (∀ Q : Quad,
          (∀ i : Fin n, toMatrix Q i i = 0) ∧
          (∀ i j : Fin n, toMatrix Q i j = toMatrix Q j i)),
      toMatrix 0 = 0 ∧
        Function.Bijective (fun Q : Quad =>
          (⟨toMatrix Q, htoMatrix Q⟩ : AltMat))) := by
  classical
    let Quad := (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2
    let AltMat :=
      {A : Matrix (Fin n) (Fin n) (ZMod 2) //
        (∀ i : Fin n, A i i = 0) ∧
        (∀ i j : Fin n, A i j = A j i)}
    let toMatrix : Quad → Matrix (Fin n) (Fin n) (ZMod 2) := fun Q =>
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0)
    let htoMatrix :
        ∀ Q : Quad,
          (∀ i : Fin n, toMatrix Q i i = 0) ∧
          (∀ i j : Fin n, toMatrix Q i j = toMatrix Q j i) := by
      intro Q
      constructor
      · intro i
        simp [toMatrix]
      · intro i j
        dsimp [toMatrix]
        by_cases hij : (i : ℕ) < (j : ℕ)
        · have hji : ¬ (j : ℕ) < (i : ℕ) := fun h => Nat.lt_asymm hij h
          simp [hij, hji]
        · by_cases hji : (j : ℕ) < (i : ℕ)
          · simp [hij, hji]
          · simp [hij, hji]
    use htoMatrix
    constructor
    · ext i j
      dsimp [toMatrix]
      by_cases hij : (i : ℕ) < (j : ℕ)
      · simp [hij]
      · by_cases hji : (j : ℕ) < (i : ℕ)
        · simp [hij, hji]
        · simp [hij, hji]
    · have raw_injective :
          Function.Injective
            (fun Q : Quad => (toMatrix Q : Matrix (Fin n) (Fin n) (ZMod 2))) := by
        simpa [Quad, toMatrix] using upper_triangular_quadratic_coeff_to_alt_matrix_injective_q2 n
      constructor
      · intro Q R hQR
        apply raw_injective
        exact congrArg (fun A : AltMat => A.1) hQR
      · intro A
        let fromAltMat : Quad := fun i j => A.1 i j.1
        use fromAltMat
        apply Subtype.ext
        ext i j
        dsimp [fromAltMat, toMatrix]
        by_cases hij : (i : ℕ) < (j : ℕ)
        · simp [hij]
        · by_cases hji : (j : ℕ) < (i : ℕ)
          · simp [hij, hji, A.2.2 j i]
          · have hle_ij : (i : ℕ) ≤ (j : ℕ) := le_of_not_gt hji
            have hle_ji : (j : ℕ) ≤ (i : ℕ) := le_of_not_gt hij
            have hnat : (i : ℕ) = (j : ℕ) := le_antisymm hle_ij hle_ji
            have hfin : i = j := Fin.ext hnat
            have hdiag : A.1 i j = 0 := by
              subst j
              exact A.2.1 i
            simp [hij, hji, hdiag]


theorem upperTriangular_canonical_nonzero_rankWeight_sum_add_affine_eq_closed_q2
    (n : ℕ) :
    (let toMatrix :
        (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) →
          Matrix (Fin n) (Fin n) (ZMod 2)) := fun Q =>
        (fun i j : Fin n =>
          if h : (i : ℕ) < (j : ℕ) then
            Q i ⟨j, h⟩
          else if h' : (j : ℕ) < (i : ℕ) then
            Q j ⟨i, h'⟩
          else
            0);
      (Finset.range (n + 1)).sum (fun r : ℕ =>
        Fintype.card
          {Q : {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} //
            Module.finrank (ZMod 2)
              (LinearMap.range ((toMatrix Q.1).toLin')) = 2 * r} *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) +
        2 * (2 ^ n - 1)
      =
      (Finset.range (n + 1)).sum (fun r : ℕ =>
        ((2 ^ (r * (r - 1)) *
            (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
          ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)))) := by
  simpa only using
      (match upper_triangular_quadratic_coeff_to_alt_matrix_bijective_q2 n with
      | ⟨htoMatrix, ⟨hzero, hbij⟩⟩ =>
          upperTriangular_nonzero_rankWeight_sum_add_affine_eq_closed_q2 n
            (fun Q :
                ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) =>
              fun i j : Fin n =>
                if h : (i : ℕ) < (j : ℕ) then
                  Q i ⟨j, h⟩
                else if h' : (j : ℕ) < (i : ℕ) then
                  Q j ⟨i, h'⟩
                else
                  0)
            htoMatrix hzero hbij)


theorem upper_triangular_nonzero_balanced_affine_param_card_closed_q2
    (n : ℕ) :
    (let Quad :=
      (i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2;
     let AffineParam := (Fin n → ZMod 2) × ZMod 2;
     let _toMatrix : Quad → Matrix (Fin n) (Fin n) (ZMod 2) := fun Q =>
      (fun i j : Fin n =>
        if h : (i : ℕ) < (j : ℕ) then
          Q i ⟨j, h⟩
        else if h' : (j : ℕ) < (i : ℕ) then
          Q j ⟨i, h'⟩
        else
          0);
     let BalancedAffineParam : Quad → AffineParam → Prop := fun Q b =>
      Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if
          (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              Q i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => b.1 i * x i) + b.2 = 0)
        then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0;
     Fintype.card
       {p : {Q : Quad // Q ≠ 0} × AffineParam //
         BalancedAffineParam p.1.1 p.2} + 2 * (2 ^ n - 1)
      =
     (Finset.range (n + 1)).sum (fun r : ℕ =>
       ((2 ^ (r * (r - 1)) *
           (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
         ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
         (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)))) := by
  exact Eq.trans
      (upper_triangular_nonzero_balanced_affine_param_card_add_affine_eq_rank_weight_sum_add_affine_q2 n)
      (upperTriangular_canonical_nonzero_rankWeight_sum_add_affine_eq_closed_q2 n)
































































































theorem quadraticANF_balancedEvalRange_card_eq_nonzeroUpperTriangular_balancedAffineParam_add_affine_q2
    (n : ℕ) :
    Fintype.card
      (Set.range
        (fun q :
          {p :
            (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
              (Fin n → ZMod 2) × ZMod 2) //
            Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
              if (Finset.univ.sum (fun i : Fin n =>
                    Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                      p.1 i j * x i * x j.1)) +
                  Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
                (1 : ℤ)
              else
                (-1 : ℤ)) = 0} =>
          fun x : (Fin n → ZMod 2) =>
            Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                q.1.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => q.1.2.1 i * x i) + q.1.2.2))
      = Fintype.card
          {p :
            {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} ×
              ((Fin n → ZMod 2) × ZMod 2) //
            Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
              if (Finset.univ.sum (fun i : Fin n =>
                    Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                      p.1.1 i j * x i * x j.1)) +
                  Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
                (1 : ℤ)
              else
                (-1 : ℤ)) = 0} +
        2 * (2 ^ n - 1) := by
  calc
      Fintype.card
          (Set.range
            (fun q :
              {p :
                (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
                  (Fin n → ZMod 2) × ZMod 2) //
                Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
                  if (Finset.univ.sum (fun i : Fin n =>
                        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                          p.1 i j * x i * x j.1)) +
                      Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0} =>
              fun x : (Fin n → ZMod 2) =>
                Finset.univ.sum (fun i : Fin n =>
                  Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                    q.1.1 i j * x i * x j.1)) +
                  Finset.univ.sum (fun i : Fin n => q.1.2.1 i * x i) + q.1.2.2))
          =
          Fintype.card
            {p :
              (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
                (Fin n → ZMod 2) × ZMod 2) //
              Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
                if (Finset.univ.sum (fun i : Fin n =>
                      Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                        p.1 i j * x i * x j.1)) +
                    Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0} := by
        exact quadraticANF_balancedCoeff_evalRange_card_eq n
      _ =
          Fintype.card
            {p :
              (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
                (Fin n → ZMod 2) × ZMod 2) //
              p.1 ≠ 0 ∧
                Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
                  if (Finset.univ.sum (fun i : Fin n =>
                        Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                          p.1 i j * x i * x j.1)) +
                      Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
                    (1 : ℤ)
                  else
                    (-1 : ℤ)) = 0} +
            2 * (2 ^ n - 1) := by
        exact quadraticANF_balancedCoeff_card_eq_nonzeroQuadratic_add_affine n
      _ =
          Fintype.card
            {p :
              {Q : ((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) // Q ≠ 0} ×
                ((Fin n → ZMod 2) × ZMod 2) //
              Finset.univ.sum (fun x : (Fin n → ZMod 2) =>
                if (Finset.univ.sum (fun i : Fin n =>
                      Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                        p.1.1 i j * x i * x j.1)) +
                    Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
                  (1 : ℤ)
                else
                  (-1 : ℤ)) = 0} +
            2 * (2 ^ n - 1) := by
        congr 1
        exact Fintype.card_congr
          { toFun := fun s =>
              ⟨(⟨s.1.1, s.2.1⟩, s.1.2), s.2.2⟩
            invFun := fun t =>
              ⟨(t.1.1.1, t.1.2), ⟨t.1.1.2, t.2⟩⟩
            left_inv := by
              intro s
              rcases s with ⟨⟨Q, b⟩, hQ, hb⟩
              rfl
            right_inv := by
              intro t
              rcases t with ⟨⟨⟨Q, hQ⟩, b⟩, hb⟩
              rfl }












theorem quadraticANF_balancedEvalRange_card_closed_q2
    (n : ℕ) :
    (let Coeff :=
      (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
        (Fin n → ZMod 2) × ZMod 2);
     let Balanced : Coeff → Prop := fun p =>
      (Finset.univ.sum (fun x : Fin n → ZMod 2 =>
        if (Finset.univ.sum (fun i : Fin n =>
            Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
              p.1 i j * x i * x j.1)) +
            Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0) then
          (1 : ℤ)
        else
          (-1 : ℤ)) = 0);
     let Eval : {p : Coeff // Balanced p} → ((Fin n → ZMod 2) → ZMod 2) := fun q =>
      fun x : Fin n → ZMod 2 =>
        (Finset.univ.sum (fun i : Fin n =>
          Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
            q.1.1 i j * x i * x j.1)) +
          Finset.univ.sum (fun i : Fin n => q.1.2.1 i * x i) + q.1.2.2);
     Fintype.card (Set.range Eval)) =
      (Finset.range (n + 1)).sum (fun r : ℕ =>
        ((2 ^ (r * (r - 1)) *
            (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
          ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
        (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) := by
  simpa using (quadraticANF_balancedEvalRange_card_eq_nonzeroUpperTriangular_balancedAffineParam_add_affine_q2 n).trans (upper_triangular_nonzero_balanced_affine_param_card_closed_q2 n)




theorem quadraticANF_exactDegreeTwoCoeff_card_closed_q2
    (n : ℕ) :
    Fintype.card
      {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        p.1 ≠ 0 ∧
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if
            (Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0)
          then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0} =
      (Finset.range (n + 1)).sum (fun r : ℕ =>
        ((2 ^ (r * (r - 1)) *
              (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
            ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1))) -
        2 * (2 ^ n - 1) := by
  let total : ℕ :=
      (Finset.range (n + 1)).sum (fun r : ℕ =>
        ((2 ^ (r * (r - 1)) *
              (Finset.range (2 * r)).prod (fun i : ℕ => 2 ^ (n - i) - 1)) /
            ((Finset.range r).prod (fun i : ℕ => 2 ^ (2 * (i + 1)) - 1))) *
          (2 ^ (2 * r + 1) * (2 ^ (n - 2 * r) - 1)))
  have hEvalRange := quadraticANF_balancedEvalRange_card_closed_q2 n
  have hCoeffEval := quadraticANF_balancedCoeff_evalRange_card_eq n
  have htotal :
      Fintype.card {p : (((i : Fin n) → {j : Fin n // (i : ℕ) < (j : ℕ)} → ZMod 2) ×
          (Fin n → ZMod 2) × ZMod 2) //
        Finset.univ.sum (fun x : Fin n → ZMod 2 =>
          if Finset.univ.sum (fun i : Fin n =>
              Finset.univ.sum (fun j : {j : Fin n // (i : ℕ) < (j : ℕ)} =>
                p.1 i j * x i * x j.1)) +
              Finset.univ.sum (fun i : Fin n => p.2.1 i * x i) + p.2.2 = 0 then
            (1 : ℤ)
          else
            (-1 : ℤ)) = 0}
        = total := by
    exact hCoeffEval.symm.trans hEvalRange
  exact quadraticANF_exactDegreeTwoCoeff_card_eq_closedTotal_sub_affine_of_total
    n total htotal


end LeanCipher.GeneratedVerifiedLemmas

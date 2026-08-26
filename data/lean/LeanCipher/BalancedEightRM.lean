import LeanCipher.BooleanWalsh
import LeanCipher.BalancedQuadratic
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEightRM

open LeanCipher.BooleanWalsh
open LeanCipher.GeneratedVerifiedLemmas

abbrev Index := Fin 7
abbrev Vec := V 7
abbrev QuadraticCoeff :=
  (i : Index) -> {j : Index // (i : Nat) < (j : Nat)} -> ZMod 2

private abbrev QuadraticCoeffN (n : Nat) :=
  (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2

private abbrev reflectedMatrix (n : Nat) (Q : QuadraticCoeffN n) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j =>
    if h : (i : Nat) < (j : Nat) then Q i ⟨j, h⟩
    else if h' : (j : Nat) < (i : Nat) then Q j ⟨i, h'⟩
    else 0

private def quadraticPhase (n : Nat) (Q : QuadraticCoeffN n)
    (a x : Fin n -> ZMod 2) : ZMod 2 :=
  (∑ i : Fin n, ∑ j : {j : Fin n // (i : Nat) < (j : Nat)},
      Q i j * x i * x j.1) +
    ∑ i : Fin n, a i * x i

private def quadraticWalsh (n : Nat) (Q : QuadraticCoeffN n)
    (a : Fin n -> ZMod 2) : Int :=
  ∑ x : Fin n -> ZMod 2,
    if quadraticPhase n Q a x = 0 then (1 : Int) else -1

set_option maxHeartbeats 800000 in
private theorem quadraticWalsh_sq_of_rank
    (n r : Nat) (Q : QuadraticCoeffN n) (a : Fin n -> ZMod 2)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' (reflectedMatrix n Q))) = 2 * r)
    (hnonzero : quadraticWalsh n Q a ≠ 0) :
    quadraticWalsh n Q a * quadraticWalsh n Q a =
      (2 ^ (2 * n - 2 * r) : Int) := by
  classical
  have hker : ∀ y : Fin n -> ZMod 2,
      (Matrix.toLin' (reflectedMatrix n Q)) y = 0 ->
        quadraticPhase n Q a y = 0 := by
    intro y hy
    exact (upperTriangular_walsh_nonzero_iff_vanishes_on_kernel_q2 n Q a).1
      (by simpa [quadraticWalsh, quadraticPhase, reflectedMatrix] using hnonzero) y
      (by simpa [reflectedMatrix] using hy)
  have hsquare := f2_function_sum_square_reindex_add n
    (fun x : Fin n -> ZMod 2 =>
      if quadraticPhase n Q a x = 0 then (1 : Int) else -1)
  rw [show quadraticWalsh n Q a = Finset.univ.sum
      (fun x : Fin n -> ZMod 2 =>
        if quadraticPhase n Q a x = 0 then (1 : Int) else -1) by rfl]
  rw [hsquare]
  have hcorr (z : Fin n -> ZMod 2) :
      Finset.univ.sum (fun x : Fin n -> ZMod 2 =>
        (if quadraticPhase n Q a (x + z) = 0 then (1 : Int) else -1) *
        (if quadraticPhase n Q a x = 0 then (1 : Int) else -1)) =
      if (Matrix.toLin' (reflectedMatrix n Q)) z = 0
      then (2 ^ n : Int) else 0 := by
    by_cases hz : (Matrix.toLin' (reflectedMatrix n Q)) z = 0
    · rw [if_pos hz]
      simpa [quadraticPhase, reflectedMatrix,
        show Fintype.card (Fin n -> ZMod 2) = 2 ^ n by simp [ZMod.card]] using
        upper_triangular_kernel_phase_pair_sign_sum_eq_card_q2 n Q a z
          (by simpa [reflectedMatrix] using hz) (hker z hz)
    · rw [if_neg hz]
      simpa [quadraticPhase, reflectedMatrix] using
        upper_triangular_nonkernel_phase_pair_sign_sum_eq_zero_q2 n Q a z
          (by simpa [reflectedMatrix] using hz)
  simp_rw [hcorr]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hkerFinrank : Module.finrank (ZMod 2)
      (LinearMap.ker (Matrix.toLin' (reflectedMatrix n Q))) = n - 2 * r := by
    have hdim := LinearMap.finrank_range_add_finrank_ker
      (Matrix.toLin' (reflectedMatrix n Q))
    have hdomain : Module.finrank (ZMod 2) (Fin n -> ZMod 2) = n := by simp
    omega
  have hkerCard :
      Fintype.card (LinearMap.ker (Matrix.toLin' (reflectedMatrix n Q))) =
        2 ^ (n - 2 * r) := by
    rw [Module.card_eq_pow_finrank
      (K := ZMod 2)
      (V := (LinearMap.ker (Matrix.toLin' (reflectedMatrix n Q)) :
        Submodule (ZMod 2) (Fin n -> ZMod 2))), hkerFinrank]
    norm_num [ZMod.card]
  have hfilterCard :
      (Finset.univ.filter (fun z : Fin n -> ZMod 2 =>
        (Matrix.toLin' (reflectedMatrix n Q)) z = 0)).card =
      Fintype.card (LinearMap.ker (Matrix.toLin' (reflectedMatrix n Q))) := by
    rw [← Fintype.card_subtype (fun z : Fin n -> ZMod 2 =>
      (Matrix.toLin' (reflectedMatrix n Q)) z = 0)]
    apply Fintype.card_congr
    exact
      { toFun := fun z => ⟨z.1, LinearMap.mem_ker.mpr z.2⟩
        invFun := fun z => ⟨z.1, LinearMap.mem_ker.mp z.2⟩
        left_inv := fun z => by cases z; rfl
        right_inv := fun z => by cases z; rfl }
  rw [hfilterCard, hkerCard]
  norm_num [pow_add]
  have hrle : 2 * r ≤ n := by
    rw [← hrank]
    exact reflected_matrix_rank_le_card_q2 n Q
  rw [show 2 * n - 2 * r = (n - 2 * r) + n by omega, pow_add]

private theorem quadraticWalsh_eq_or_eq_neg_amplitude
    (n r : Nat) (Q : QuadraticCoeffN n) (a : Fin n -> ZMod 2)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' (reflectedMatrix n Q))) = 2 * r)
    (hnonzero : quadraticWalsh n Q a ≠ 0) :
    quadraticWalsh n Q a = (2 ^ (n - r) : Int) ∨
      quadraticWalsh n Q a = -(2 ^ (n - r) : Int) := by
  have hrle : r ≤ n := by
    have h := rank_even_bound_from_reflected_rank_q2 n r Q
      (by simpa [reflectedMatrix] using hrank)
    omega
  have hsquare := quadraticWalsh_sq_of_rank n r Q a hrank hnonzero
  have hpowsq : (2 ^ (n - r) : Int) * (2 ^ (n - r) : Int) =
      (2 ^ (2 * n - 2 * r) : Int) := by
    rw [← pow_add]
    congr 2
    omega
  exact mul_self_eq_mul_self_iff.mp (hsquare.trans hpowsq.symm)

def booleanPoint (S : Finset Index) : Vec :=
  fun i => if i ∈ S then 1 else 0

def booleanSupport (x : Vec) : Finset Index :=
  Finset.univ.filter fun i => x i = 1

def monomialEval (S : Finset Index) (x : Vec) : ZMod 2 :=
  S.prod fun i => x i

def anfCoeff (f : Vec -> ZMod 2) (S : Finset Index) : ZMod 2 :=
  S.powerset.sum fun T => f (booleanPoint T)

def quadraticEval (Q : QuadraticCoeff) (a : Vec) (c : ZMod 2)
    (x : Vec) : ZMod 2 :=
  (∑ i : Index, ∑ j : {j : Index // (i : Nat) < (j : Nat)},
      Q i j * x i * x j.1) +
    (∑ i : Index, a i * x i) + c

def intParity (v : Vec -> Int) : Vec -> ZMod 2 :=
  fun x => (v x : ZMod 2)

def subcube (S : Finset Index) : Finset Vec :=
  Finset.univ.filter fun x => ∀ i, i ∉ S -> x i = 0

@[simp] theorem booleanPoint_apply (S : Finset Index) (i : Index) :
    booleanPoint S i = if i ∈ S then 1 else 0 := rfl

theorem zmod2_eq_zero_or_one' (z : ZMod 2) : z = 0 ∨ z = 1 := by
  exact zmod2_eq_zero_or_one z

@[simp] theorem booleanPoint_booleanSupport (x : Vec) :
    booleanPoint (booleanSupport x) = x := by
  funext i
  rcases zmod2_eq_zero_or_one' (x i) with h | h
  · simp [booleanPoint, booleanSupport, h]
  · simp [booleanPoint, booleanSupport, h]

@[simp] theorem booleanSupport_booleanPoint (S : Finset Index) :
    booleanSupport (booleanPoint S) = S := by
  ext i
  simp [booleanSupport, booleanPoint]

theorem powerset_mobius_involution
    {A : Type*} [CommRing A] [CharP A 2]
    (f : Finset Index -> A) (S : Finset Index) :
    (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, f U) = f S := by
  induction S using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_powerset_insert ha, ih]
      have hsplit :
          (∑ T ∈ S.powerset, ∑ U ∈ (insert a T).powerset, f U) =
            (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, f U) +
              ∑ T ∈ S.powerset, ∑ U ∈ T.powerset, f (insert a U) := by
        calc
          _ = ∑ T ∈ S.powerset,
                ((∑ U ∈ T.powerset, f U) +
                  ∑ U ∈ T.powerset, f (insert a U)) := by
                apply Finset.sum_congr rfl
                intro T hT
                exact Finset.sum_powerset_insert
                  (Finset.notMem_of_mem_powerset_of_notMem hT ha) f
          _ = _ := by rw [Finset.sum_add_distrib]
      rw [hsplit, ih, ih, <- add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem anf_reconstruction (f : Vec -> ZMod 2) (x : Vec) :
    (∑ S ∈ (booleanSupport x).powerset, anfCoeff f S) = f x := by
  rw [show f x = f (booleanPoint (booleanSupport x)) by simp]
  exact powerset_mobius_involution
    (fun T => f (booleanPoint T)) (booleanSupport x)

@[simp] theorem monomialEval_eq_indicator (S : Finset Index) (x : Vec) :
    monomialEval S x = if S ⊆ booleanSupport x then 1 else 0 := by
  classical
  by_cases hS : S ⊆ booleanSupport x
  · rw [if_pos hS]
    apply Finset.prod_eq_one
    intro i hi
    have hiSupport := hS hi
    simpa [monomialEval, booleanSupport] using
      (Finset.mem_filter.mp hiSupport).2
  · rw [if_neg hS]
    obtain ⟨i, hiS, hiSupport⟩ := Finset.not_subset.mp hS
    apply Finset.prod_eq_zero hiS
    have hxi : x i ≠ 1 := by
      simpa [booleanSupport] using hiSupport
    rcases zmod2_eq_zero_or_one' (x i) with hxi0 | hxi1
    · exact hxi0
    · exact (hxi hxi1).elim

theorem anf_reconstruction_monomial (f : Vec -> ZMod 2) (x : Vec) :
    (∑ S : Finset Index, anfCoeff f S * monomialEval S x) = f x := by
  classical
  rw [← anf_reconstruction f x]
  calc
    (∑ S : Finset Index, anfCoeff f S * monomialEval S x) =
        ∑ S : Finset Index,
          if S ⊆ booleanSupport x then anfCoeff f S else 0 := by
            apply Finset.sum_congr rfl
            intro S _
            simp [monomialEval_eq_indicator]
    _ = ∑ S ∈ (booleanSupport x).powerset, anfCoeff f S := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext S
            simp
          · intro S _
            rfl

theorem sum_card_zero (F : Finset Index -> ZMod 2) :
    (∑ S : Finset Index, if S.card = 0 then F S else 0) = F ∅ := by
  classical
  rw [← Finset.sum_filter]
  have hempty :
      (Finset.univ.filter fun S : Finset Index => S.card = 0) = {∅} := by
    ext S
    simp [Finset.card_eq_zero]
  rw [hempty]
  simp

theorem sum_card_one (F : Finset Index -> ZMod 2) :
    (∑ S : Finset Index, if S.card = 1 then F S else 0) =
      ∑ i : Index, F {i} := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => {i})
  · intro i _
    simp
  · intro i _ j _ hij
    simpa using hij
  · intro S hS
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hS).2
    exact ⟨i, by simp⟩
  · intro i _
    rfl

theorem sum_card_two (F : Finset Index -> ZMod 2) :
    (∑ S : Finset Index, if S.card = 2 then F S else 0) =
      ∑ i : Index, ∑ j : {j : Index // (i : Nat) < (j : Nat)}, F {i, j.1} := by
  classical
  rw [← Finset.sum_filter]
  calc
    (∑ S ∈ (Finset.univ.filter fun S : Finset Index => S.card = 2), F S) =
        ∑ p : (Σ i : Index, {j : Index // (i : Nat) < (j : Nat)}),
          F {p.1, p.2.1} := by
      symm
      apply Finset.sum_bij (fun p _ => {p.1, p.2.1})
      · rintro ⟨i, j⟩ _
        have hij : i ≠ j.1 := by
          intro hij
          have hijVal := congrArg Fin.val hij
          omega
        simp [hij]
      · rintro ⟨i, j⟩ _ ⟨k, l⟩ _ hpairs
        have hi : i = k ∨ i = l.1 := by
          have : i ∈ ({k, l.1} : Finset Index) := by
            rw [← hpairs]
            simp
          simpa [eq_comm] using this
        have hk : k = i ∨ k = j.1 := by
          have : k ∈ ({i, j.1} : Finset Index) := by
            rw [hpairs]
            simp
          simpa [eq_comm] using this
        have hik : i = k := by
          rcases hi with hik | hil
          · exact hik
          · rcases hk with hki | hkj
            · have hilVal := congrArg Fin.val hil
              have hkiVal := congrArg Fin.val hki
              exfalso
              omega
            · have hilVal := congrArg Fin.val hil
              have hkjVal := congrArg Fin.val hkj
              exfalso
              omega
        subst k
        have hjl : j.1 = l.1 := by
          have : j.1 ∈ ({i, l.1} : Finset Index) := by
            rw [← hpairs]
            simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with hji | hjl
          · have hjiVal := congrArg Fin.val hji
            exfalso
            omega
          · exact hjl
        cases Subtype.ext hjl
        rfl
      · intro S hS
        obtain ⟨x, y, hxy, rfl⟩ :=
          Finset.card_eq_two.mp (Finset.mem_filter.mp hS).2
        rcases lt_or_gt_of_ne hxy with hxy' | hyx'
        · exact ⟨⟨x, ⟨y, hxy'⟩⟩, by simp⟩
        · exact ⟨⟨y, ⟨x, hyx'⟩⟩, by simp [Finset.pair_comm]⟩
      · rintro ⟨i, j⟩ _
        rfl
    _ = ∑ i : Index,
        ∑ j : {j : Index // (i : Nat) < (j : Nat)}, F {i, j.1} := by
      rw [Fintype.sum_sigma]

theorem booleanPoint_mem_subcube_iff (S T : Finset Index) :
    booleanPoint T ∈ subcube S ↔ T ⊆ S := by
  constructor
  · intro h i hiT
    by_contra hiS
    have hz := (Finset.mem_filter.mp h).2 i hiS
    simp [booleanPoint, hiT] at hz
  · intro h
    simp only [subcube, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hiS
    have hiT : i ∉ T := fun hi => hiS (h hi)
    simp [booleanPoint, hiT]

theorem sum_subcube_eq_sum_powerset (v : Vec -> Int) (S : Finset Index) :
    (∑ x ∈ subcube S, v x) = ∑ T ∈ S.powerset, v (booleanPoint T) := by
  classical
  symm
  apply Finset.sum_bij (fun T _ => booleanPoint T)
  · intro T hT
    exact booleanPoint_mem_subcube_iff S T |>.2 (Finset.mem_powerset.mp hT)
  · intro T hT U hU hEq
    simpa using congrArg booleanSupport hEq
  · intro x hx
    refine ⟨booleanSupport x, ?_⟩
    have hxzero := (Finset.mem_filter.mp hx).2
    have hsubset : booleanSupport x ⊆ S := by
      intro i hi
      by_contra hiS
      have hxi := hxzero i hiS
      have hiOne : x i = 1 := (Finset.mem_filter.mp hi).2
      simp [hiOne] at hxi
    exact ⟨Finset.mem_powerset.mpr hsubset, booleanPoint_booleanSupport x⟩
  · intro T hT
    rfl

theorem f2Dot_booleanPoint (S : Finset Index) (x : Vec) :
    f2Dot (booleanPoint S) x = ∑ i ∈ S, x i := by
  classical
  simp [f2Dot, booleanPoint]

theorem sign_sum (S : Finset Index) (g : Index -> ZMod 2) :
    sign (∑ i ∈ S, g i) = ∏ i ∈ S, sign (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]

theorem character_booleanPoint (S : Finset Index) (x : Vec) :
    character (booleanPoint S) x = ∏ i ∈ S, sign (x i) := by
  rw [character, f2Dot_booleanPoint]
  exact sign_sum S x

theorem powerset_character_sum (S : Finset Index) (x : Vec) :
    (∑ T ∈ (Finset.univ \ S).powerset, character (booleanPoint T) x) =
      if x ∈ subcube S then (2 : Int) ^ (Finset.univ \ S).card else 0 := by
  classical
  rw [show (∑ T ∈ (Finset.univ \ S).powerset, character (booleanPoint T) x) =
      ∑ T ∈ (Finset.univ \ S).powerset, ∏ i ∈ T, sign (x i) by
        apply Finset.sum_congr rfl
        intro T _
        exact character_booleanPoint T x]
  rw [← Finset.prod_one_add]
  by_cases hx : x ∈ subcube S
  · rw [if_pos hx]
    have hxzero := (Finset.mem_filter.mp hx).2
    calc
      (Finset.univ \ S).prod (fun i => (1 : Int) + sign (x i)) =
          (Finset.univ \ S).prod (fun _i => (2 : Int)) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
            rw [hxzero i hiS]
            simp
      _ = (2 : Int) ^ (Finset.univ \ S).card := by simp
  · rw [if_neg hx]
    have hexists : ∃ i : Index, i ∉ S ∧ x i ≠ 0 := by
      simpa [subcube] using hx
    obtain ⟨i, hiS, hxi⟩ := hexists
    apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiS⟩)
    simp [sign, hxi]

theorem sum_hadamard_over_complement (v : Vec -> Int) (S : Finset Index) :
    (∑ T ∈ (Finset.univ \ S).powerset,
        hadamardTransform (fun a x : Vec => character a x) v (booleanPoint T)) =
      (2 : Int) ^ (Finset.univ \ S).card *
        (∑ T ∈ S.powerset, v (booleanPoint T)) := by
  classical
  calc
    (∑ T ∈ (Finset.univ \ S).powerset,
        hadamardTransform (fun a x : Vec => character a x) v (booleanPoint T)) =
        ∑ T ∈ (Finset.univ \ S).powerset, ∑ x : Vec,
          character (booleanPoint T) x * v x := by rfl
    _ = ∑ x : Vec, ∑ T ∈ (Finset.univ \ S).powerset,
          character (booleanPoint T) x * v x := by
          rw [Finset.sum_comm]
    _ = ∑ x : Vec,
          (∑ T ∈ (Finset.univ \ S).powerset,
            character (booleanPoint T) x) * v x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
    _ = ∑ x : Vec,
          (if x ∈ subcube S then (2 : Int) ^ (Finset.univ \ S).card else 0) * v x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [powerset_character_sum]
    _ = ∑ x ∈ subcube S, (2 : Int) ^ (Finset.univ \ S).card * v x := by
          simp
    _ = (2 : Int) ^ (Finset.univ \ S).card * ∑ x ∈ subcube S, v x := by
          rw [Finset.mul_sum]
    _ = (2 : Int) ^ (Finset.univ \ S).card *
          (∑ T ∈ S.powerset, v (booleanPoint T)) := by
          rw [sum_subcube_eq_sum_powerset]

theorem thirtyTwo_dvd_scaled_anf_sum
    (v : Vec -> Int)
    (hdiv : ∀ a : Vec,
      (32 : Int) ∣ hadamardTransform (fun a x : Vec => character a x) v a)
    (S : Finset Index) :
    (32 : Int) ∣ (2 : Int) ^ (Finset.univ \ S).card *
      (∑ T ∈ S.powerset, v (booleanPoint T)) := by
  rw [← sum_hadamard_over_complement v S]
  apply Finset.dvd_sum
  intro T hT
  exact hdiv (booleanPoint T)

theorem anf_integer_sum_even_of_three_le_card
    (v : Vec -> Int)
    (hdiv : ∀ a : Vec,
      (32 : Int) ∣ hadamardTransform (fun a x : Vec => character a x) v a)
    (S : Finset Index) (hS : 3 ≤ S.card) :
    Even (∑ T ∈ S.powerset, v (booleanPoint T)) := by
  have hcard : (Finset.univ \ S).card ≤ 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, hk⟩ := thirtyTwo_dvd_scaled_anf_sum v hdiv S
  interval_cases hc : (Finset.univ \ S).card <;>
    norm_num at hk <;> exact even_iff_two_dvd.mpr (by omega)

theorem anfCoeff_eq_zero_of_three_le_card
    (v : Vec -> Int)
    (hdiv : ∀ a : Vec,
      (32 : Int) ∣ hadamardTransform (fun a x : Vec => character a x) v a)
    (S : Finset Index) (hS : 3 ≤ S.card) :
    anfCoeff (intParity v) S = 0 := by
  obtain ⟨k, hk⟩ := anf_integer_sum_even_of_three_le_card v hdiv S hS
  simp only [anfCoeff, intParity]
  rw [← Int.cast_sum]
  rw [hk]
  push_cast
  exact CharTwo.add_self_eq_zero _

theorem exists_quadratic_representation_of_high_anf_zero
    (f : Vec -> ZMod 2)
    (hhigh : ∀ S : Finset Index, 3 ≤ S.card -> anfCoeff f S = 0) :
    ∃ Q : QuadraticCoeff, ∃ a : Vec, ∃ c : ZMod 2,
      ∀ x, f x = quadraticEval Q a c x := by
  let Q : QuadraticCoeff := fun i j => anfCoeff f {i, j.1}
  let a : Vec := fun i => anfCoeff f {i}
  let c : ZMod 2 := anfCoeff f ∅
  refine ⟨Q, a, c, ?_⟩
  intro x
  let term : Finset Index -> ZMod 2 :=
    fun S => anfCoeff f S * monomialEval S x
  have hempty : term ∅ = c := by
    simp [term, c, monomialEval]
  have hsingleton (i : Index) : term {i} = a i * x i := by
    simp [term, a, monomialEval]
  have hpair (i : Index) (j : {j : Index // (i : Nat) < (j : Nat)}) :
      term {i, j.1} = Q i j * x i * x j.1 := by
    have hij : i ≠ j.1 := by
      intro hij
      have hijVal := congrArg Fin.val hij
      omega
    simp [term, Q, monomialEval, hij]
    ring
  have hsplit (S : Finset Index) :
      term S =
        (if S.card = 0 then term S else 0) +
        (if S.card = 1 then term S else 0) +
        (if S.card = 2 then term S else 0) := by
    by_cases h0 : S.card = 0
    · simp [h0]
    by_cases h1 : S.card = 1
    · simp [h1]
    by_cases h2 : S.card = 2
    · simp [h2]
    have h3 : 3 ≤ S.card := by omega
    rw [show term S = 0 by simp [term, hhigh S h3]]
    simp [h0, h1, h2]
  calc
    f x = ∑ S : Finset Index, term S := by
      simpa [term] using (anf_reconstruction_monomial f x).symm
    _ = ∑ S : Finset Index,
          ((if S.card = 0 then term S else 0) +
            (if S.card = 1 then term S else 0) +
            (if S.card = 2 then term S else 0)) := by
          apply Finset.sum_congr rfl
          intro S _
          exact hsplit S
    _ = (∑ S : Finset Index, if S.card = 0 then term S else 0) +
          (∑ S : Finset Index, if S.card = 1 then term S else 0) +
          (∑ S : Finset Index, if S.card = 2 then term S else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = term ∅ + (∑ i : Index, term {i}) +
          ∑ i : Index,
            ∑ j : {j : Index // (i : Nat) < (j : Nat)}, term {i, j.1} := by
          rw [sum_card_zero, sum_card_one, sum_card_two]
    _ = quadraticEval Q a c x := by
          rw [hempty]
          simp_rw [hsingleton, hpair]
          simp only [quadraticEval]
          ac_rfl

theorem exists_quadratic_representation_of_hadamard_dvd
    (v : Vec -> Int)
    (hdiv : ∀ a : Vec,
      (32 : Int) ∣ hadamardTransform (fun a x : Vec => character a x) v a) :
    ∃ Q : QuadraticCoeff, ∃ a : Vec, ∃ c : ZMod 2,
      ∀ x, intParity v x = quadraticEval Q a c x := by
  apply exists_quadratic_representation_of_high_anf_zero (intParity v)
  intro S hS
  exact anfCoeff_eq_zero_of_three_le_card v hdiv S hS

theorem signed_sum_quadratic_constant
    (Q : QuadraticCoeff) (a : Vec) (c : ZMod 2) :
    (∑ x : Vec, sign (quadraticEval Q a c x)) =
      if c = 0 then quadraticWalsh 7 Q a else -quadraticWalsh 7 Q a := by
  classical
  change (∑ x : Vec,
      sign (quadraticPhase 7 Q a x + c)) = _
  by_cases hc : c = 0
  · subst c
    simp [quadraticWalsh, sign]
  · have hc1 : c = 1 := zmod2_eq_one_of_ne_zero hc
    subst c
    rw [if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    simp only [quadraticWalsh]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    simp only [sign]
    have hcase : ∀ z : ZMod 2,
        (if z + 1 = 0 then (1 : Int) else -1) =
          -(if z = 0 then (1 : Int) else -1) := by decide
    exact hcase (quadraticPhase 7 Q a x)

theorem quadratic_weight_classification
    (Q : QuadraticCoeff) (a : Vec) (c : ZMod 2) :
    weight (quadraticEval Q a c) = 0 ∨
    weight (quadraticEval Q a c) = 32 ∨
    weight (quadraticEval Q a c) = 48 ∨
    weight (quadraticEval Q a c) = 56 ∨
    weight (quadraticEval Q a c) = 64 ∨
    weight (quadraticEval Q a c) = 72 ∨
    weight (quadraticEval Q a c) = 80 ∨
    weight (quadraticEval Q a c) = 96 ∨
    weight (quadraticEval Q a c) = 128 := by
  classical
  obtain ⟨sFin, hsRank⟩ := upper_triangular_reflected_rank_even_fin_q2 7 Q
  let s : Nat := sFin
  have hrank : Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' (reflectedMatrix 7 Q))) = 2 * s := by
    simpa [s, reflectedMatrix] using hsRank
  have hsle : 2 * s ≤ 7 :=
    rank_even_bound_from_reflected_rank_q2 7 s Q (by
      simpa [reflectedMatrix] using hrank)
  have hs3 : s ≤ 3 := by omega
  have hsum := sum_sign_eq_card_sub_two_mul_weight (quadraticEval Q a c)
  by_cases hphase : quadraticWalsh 7 Q a = 0
  · have hsigned : (∑ x : Vec, sign (quadraticEval Q a c x)) = 0 := by
      rw [signed_sum_quadratic_constant, hphase]
      split <;> simp
    rw [hsigned] at hsum
    right; right; right; right; left
    norm_num at hsum
    omega
  · have hamp := quadraticWalsh_eq_or_eq_neg_amplitude
      7 s Q a hrank hphase
    have hphaseAmp :
        quadraticWalsh 7 Q a =
            ((2 ^ (7 - s) : Nat) : Int) ∨
          quadraticWalsh 7 Q a =
            -((2 ^ (7 - s) : Nat) : Int) := hamp
    have hsignedAmp :
        (∑ x : Vec, sign (quadraticEval Q a c x)) =
            ((2 ^ (7 - s) : Nat) : Int) ∨
          (∑ x : Vec, sign (quadraticEval Q a c x)) =
            -((2 ^ (7 - s) : Nat) : Int) := by
      rw [signed_sum_quadratic_constant]
      rcases hphaseAmp with hpos | hneg
      · by_cases hc : c = 0
        · left
          rw [if_pos hc, hpos]
        · right
          rw [if_neg hc, hpos]
      · by_cases hc : c = 0
        · right
          rw [if_pos hc, hneg]
        · left
          rw [if_neg hc, hneg]
          simp
    interval_cases s <;>
      norm_num at hsignedAmp <;>
      rcases hsignedAmp with hW | hW <;>
      rw [hW] at hsum <;>
      norm_num at hsum ⊢ <;>
      omega

def quadraticWeightSet : Finset Nat :=
  [0, 32, 48, 56, 64, 72, 80, 96, 128].toFinset

theorem quadratic_weight_mem
    (Q : QuadraticCoeff) (a : Vec) (c : ZMod 2) :
    weight (quadraticEval Q a c) ∈ quadraticWeightSet := by
  simpa [quadraticWeightSet] using quadratic_weight_classification Q a c

theorem intParity_weight_classification_of_hadamard_dvd
    (v : Vec -> Int)
    (hdiv : ∀ a : Vec,
      (32 : Int) ∣ hadamardTransform (fun a x : Vec => character a x) v a) :
    weight (intParity v) = 0 ∨
    weight (intParity v) = 32 ∨
    weight (intParity v) = 48 ∨
    weight (intParity v) = 56 ∨
    weight (intParity v) = 64 ∨
    weight (intParity v) = 72 ∨
    weight (intParity v) = 80 ∨
    weight (intParity v) = 96 ∨
    weight (intParity v) = 128 := by
  obtain ⟨Q, a, c, hrepr⟩ :=
    exists_quadratic_representation_of_hadamard_dvd v hdiv
  have hfun : intParity v = quadraticEval Q a c := funext hrepr
  rw [hfun]
  exact quadratic_weight_classification Q a c

theorem hadamard_dvd32_implies_quadratic_and_weight_mem
    (v : Vec -> Int)
    (hdiv : ∀ a : Vec,
      (32 : Int) ∣ hadamardTransform (fun a x : Vec => character a x) v a) :
    ∃ Q : QuadraticCoeff, ∃ a : Vec, ∃ c : ZMod 2,
      (∀ x, intParity v x = quadraticEval Q a c x) ∧
        weight (intParity v) ∈ quadraticWeightSet := by
  obtain ⟨Q, a, c, hrepr⟩ :=
    exists_quadratic_representation_of_hadamard_dvd v hdiv
  refine ⟨Q, a, c, hrepr, ?_⟩
  have hfun : intParity v = quadraticEval Q a c := funext hrepr
  rw [hfun]
  exact quadratic_weight_mem Q a c

end LeanCipher.BalancedEightRM

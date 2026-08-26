import LeanCipher.BalancedQuadratic
import LeanCipher.BooleanWalsh

/-!
# Seven-variable quadratic spectra for the balanced-eight proof

This file isolates the coordinate-free Fourier facts about quadratic Boolean
functions that are used by the terminal certificates in the balanced
eight-variable nonlinearity argument.  A value of `RM2` represents a
degree-at-most-two ANF whose constant coefficient is zero.
-/

open scoped BigOperators

namespace LeanCipher.BalancedEightQuadratic

open LeanCipher.BooleanWalsh
open LeanCipher.GeneratedVerifiedLemmas

abbrev RM2Coeff (n : Nat) :=
  (i : Fin n) -> {j : Fin n // (i : Nat) < (j : Nat)} -> ZMod 2

structure RM2 (n : Nat) where
  quadratic : RM2Coeff n
  linear : V n

def quadraticEval (Q : RM2Coeff n) (x : V n) : ZMod 2 :=
  Finset.univ.sum fun i : Fin n =>
    Finset.univ.sum fun j : {j : Fin n // (i : Nat) < (j : Nat)} =>
      Q i j * x i * x j.1

def rm2Eval (R : RM2 n) (x : V n) : ZMod 2 :=
  quadraticEval R.quadratic x + f2Dot R.linear x

def polarMatrix (Q : RM2Coeff n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j =>
    if h : (i : Nat) < (j : Nat) then
      Q i ⟨j, h⟩
    else if h' : (j : Nat) < (i : Nat) then
      Q j ⟨i, h'⟩
    else
      0

noncomputable def polarRank (Q : RM2Coeff n) : Nat :=
  Module.finrank (ZMod 2)
    (LinearMap.range (Matrix.toLin' (polarMatrix Q)))

def phaseWalsh (Q : RM2Coeff n) (a : V n) : Int :=
  ∑ x : V n, sign (quadraticEval Q x + f2Dot a x)

@[simp]
theorem rm2Eval_zero (R : RM2 n) : rm2Eval R 0 = 0 := by
  simp [rm2Eval, quadraticEval, f2Dot]

theorem rm2_walsh_eq_phaseWalsh (R : RM2 n) (a : V n) :
    walsh (rm2Eval R) a = phaseWalsh R.quadratic (R.linear + a) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  simp only [rm2Eval, quadraticEval, f2Dot,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ac_rfl

private theorem phaseWalsh_ne_zero_iff_kernel
    (Q : RM2Coeff n) (a : V n) :
    phaseWalsh Q a ≠ 0 ↔
      ∀ y : V n, Matrix.toLin' (polarMatrix Q) y = 0 ->
        quadraticEval Q y + f2Dot a y = 0 := by
  simpa [phaseWalsh, polarMatrix, quadraticEval, f2Dot, sign] using
    (upperTriangular_walsh_nonzero_iff_vanishes_on_kernel_q2 n Q a)

private theorem kernel_correlation
    (Q : RM2Coeff n) (a z : V n)
    (hz : Matrix.toLin' (polarMatrix Q) z = 0)
    (hphase : quadraticEval Q z + f2Dot a z = 0) :
    (∑ x : V n,
      sign (quadraticEval Q (x + z) + f2Dot a (x + z)) *
        sign (quadraticEval Q x + f2Dot a x)) =
      (Fintype.card (V n) : Int) := by
  simpa [polarMatrix, quadraticEval, f2Dot, sign] using
    (upper_triangular_kernel_phase_pair_sign_sum_eq_card_q2 n Q a z hz hphase)

private theorem nonkernel_correlation
    (Q : RM2Coeff n) (a z : V n)
    (hz : Matrix.toLin' (polarMatrix Q) z ≠ 0) :
    (∑ x : V n,
      sign (quadraticEval Q (x + z) + f2Dot a (x + z)) *
        sign (quadraticEval Q x + f2Dot a x)) = 0 := by
  simpa [polarMatrix, quadraticEval, f2Dot, sign] using
    (upper_triangular_nonkernel_phase_pair_sign_sum_eq_zero_q2 n Q a z hz)

theorem phaseWalsh_sq_of_ne_zero
    (Q : RM2Coeff n) (a : V n) (s : Nat)
    (hrank : polarRank Q = 2 * s)
    (ha : phaseWalsh Q a ≠ 0) :
    phaseWalsh Q a ^ 2 =
      ((2 ^ (n - 2 * s) : Nat) : Int) * ((2 ^ n : Nat) : Int) := by
  classical
  let A := polarMatrix Q
  let w : V n -> Int := fun x =>
    sign (quadraticEval Q x + f2Dot a x)
  have hkernel : ∀ z : V n, Matrix.toLin' A z = 0 ->
      quadraticEval Q z + f2Dot a z = 0 := by
    simpa [A] using (phaseWalsh_ne_zero_iff_kernel Q a).mp ha
  have hcorr (z : V n) :
      (∑ x : V n, w (x + z) * w x) =
        if Matrix.toLin' A z = 0 then (Fintype.card (V n) : Int) else 0 := by
    by_cases hz : Matrix.toLin' A z = 0
    · rw [if_pos hz]
      simpa [A, w] using kernel_correlation Q a z hz (hkernel z hz)
    · rw [if_neg hz]
      simpa [A, w] using nonkernel_correlation Q a z hz
  have hkernelRank :
      Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' A)) = n - 2 * s := by
    have hdim := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
    have hrange :
        Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' A)) = 2 * s := by
      simpa [A, polarRank] using hrank
    have hdomain : Module.finrank (ZMod 2) (V n) = n := f2Vec_finrank n
    rw [hrange, hdomain] at hdim
    omega
  have hkernelCard :
      Fintype.card {z : V n // Matrix.toLin' A z = 0} = 2 ^ (n - 2 * s) := by
    rw [matrix_tolin_kernel_subtype_card_eq_two_pow_finrank]
    rw [hkernelRank]
  have hfilterCard :
      ((Finset.univ.filter fun z : V n => Matrix.toLin' A z = 0).card) =
        2 ^ (n - 2 * s) := by
    calc
      (Finset.univ.filter fun z : V n => Matrix.toLin' A z = 0).card =
          Fintype.card {z : V n // Matrix.toLin' A z = 0} := by
        symm
        exact Fintype.card_ofFinset
          (p := {z : V n | Matrix.toLin' A z = 0})
          (Finset.univ.filter fun z : V n => Matrix.toLin' A z = 0)
          (fun z => by simp)
      _ = 2 ^ (n - 2 * s) := hkernelCard
  calc
    phaseWalsh Q a ^ 2 = phaseWalsh Q a * phaseWalsh Q a := by ring
    _ = (∑ x : V n, w x) * (∑ x : V n, w x) := by
      rfl
    _ = ∑ z : V n, ∑ x : V n, w (x + z) * w x :=
      f2_function_sum_square_reindex_add n w
    _ = ∑ z : V n,
        if Matrix.toLin' A z = 0 then (Fintype.card (V n) : Int) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      exact hcorr z
    _ = ((Finset.univ.filter fun z : V n => Matrix.toLin' A z = 0).card : Int) *
        (Fintype.card (V n) : Int) := by
      calc
        (∑ z : V n,
            if Matrix.toLin' A z = 0 then (Fintype.card (V n) : Int) else 0) =
            ∑ z ∈ (Finset.univ.filter fun z : V n => Matrix.toLin' A z = 0),
              (Fintype.card (V n) : Int) := by
          symm
          exact Finset.sum_filter _ _
        _ = ((Finset.univ.filter fun z : V n => Matrix.toLin' A z = 0).card : Int) *
            (Fintype.card (V n) : Int) := by simp
    _ = ((2 ^ (n - 2 * s) : Nat) : Int) * ((2 ^ n : Nat) : Int) := by
      have hfilterCardInt :
          ((Finset.univ.filter fun z : V n => Matrix.toLin' A z = 0).card : Int) =
            ((2 ^ (n - 2 * s) : Nat) : Int) := by
        exact_mod_cast hfilterCard
      have hspaceCardInt :
          (Fintype.card (V n) : Int) = ((2 ^ n : Nat) : Int) := by
        exact_mod_cast f2Vec_card n
      rw [hfilterCardInt, hspaceCardInt]

theorem phaseWalsh_natAbs_seven
    (Q : RM2Coeff 7) (a : V 7) (s : Nat)
    (hrank : polarRank Q = 2 * s)
    (ha : phaseWalsh Q a ≠ 0) :
    (phaseWalsh Q a).natAbs = 2 ^ (7 - s) := by
  have hs : 2 * s <= 7 := by
    exact rank_even_bound_from_reflected_rank_q2 7 s Q (by
      simpa [polarRank, polarMatrix] using hrank)
  have hs' : s <= 3 := by omega
  have hsq := phaseWalsh_sq_of_ne_zero Q a s hrank ha
  interval_cases s <;>
    norm_num at hsq ⊢ <;>
    exact (Int.natAbs_eq_iff.mpr ((sq_eq_sq_iff_eq_or_eq_neg.mp (by
      simpa [pow_two] using hsq))))

def walshSupport (R : RM2 7) : Finset (V 7) :=
  Finset.univ.filter fun a => walsh (rm2Eval R) a ≠ 0

theorem walshSupport_card
    (R : RM2 7) (s : Nat) (hrank : polarRank R.quadratic = 2 * s) :
    (walshSupport R).card = 2 ^ (2 * s) := by
  classical
  have hphase :
      Fintype.card {a : V 7 // phaseWalsh R.quadratic a ≠ 0} = 2 ^ (2 * s) := by
    simpa [phaseWalsh, polarRank, polarMatrix, quadraticEval, f2Dot, sign] using
      (upperTriangular_walshSupport_card_eq_pow_rank_unconditional_q2
        7 s R.quadratic (by simpa [polarRank, polarMatrix] using hrank))
  let shift : V 7 ≃ V 7 := Equiv.addLeft R.linear
  let e : {a : V 7 // walsh (rm2Eval R) a ≠ 0} ≃
      {a : V 7 // phaseWalsh R.quadratic a ≠ 0} :=
    Equiv.subtypeEquiv shift (fun a => by
      rw [rm2_walsh_eq_phaseWalsh]
      simp [shift, Equiv.addLeft])
  calc
    (walshSupport R).card =
        Fintype.card {a : V 7 // walsh (rm2Eval R) a ≠ 0} := by
      symm
      exact Fintype.card_ofFinset
        (p := {a : V 7 | walsh (rm2Eval R) a ≠ 0})
        (walshSupport R) (fun a => by simp [walshSupport])
    _ = Fintype.card {a : V 7 // phaseWalsh R.quadratic a ≠ 0} :=
      Fintype.card_congr e
    _ = 2 ^ (2 * s) := hphase

theorem rm2_walsh_natAbs
    (R : RM2 7) (s : Nat) (hrank : polarRank R.quadratic = 2 * s)
    (a : V 7) (ha : walsh (rm2Eval R) a ≠ 0) :
    (walsh (rm2Eval R) a).natAbs = 2 ^ (7 - s) := by
  rw [rm2_walsh_eq_phaseWalsh] at ha ⊢
  exact phaseWalsh_natAbs_seven R.quadratic (R.linear + a) s hrank ha

def certificateSign (R : RM2 7) (s : Nat) (a : V 7) : Int :=
  if walsh (rm2Eval R) a = ((2 ^ (7 - s) : Nat) : Int) then -1 else 1

theorem certificateSign_eq_one_or_neg_one (R : RM2 7) (s : Nat) (a : V 7) :
    certificateSign R s a = 1 ∨ certificateSign R s a = -1 := by
  simp only [certificateSign]
  split_ifs <;> simp

theorem amplitude_mul_certificateSign
    (R : RM2 7) (s : Nat) (hrank : polarRank R.quadratic = 2 * s)
    (a : V 7) (ha : a ∈ walshSupport R) :
    ((2 ^ (7 - s) : Nat) : Int) * certificateSign R s a =
      -walsh (rm2Eval R) a := by
  have hne : walsh (rm2Eval R) a ≠ 0 := by
    simpa [walshSupport] using ha
  have habs := rm2_walsh_natAbs R s hrank a hne
  rcases Int.natAbs_eq_iff.mp habs with hpos | hneg
  · simp [certificateSign, hpos]
  · have hamp : (0 : Int) < ((2 ^ (7 - s) : Nat) : Int) := by positivity
    simp [certificateSign, hneg]

def certificateTransform (R : RM2 7) (s : Nat) (a : V 7) : Int :=
  ∑ x ∈ walshSupport R, certificateSign R s x * character a x

theorem certificateTransform_eq
    (R : RM2 7) (s : Nat) (hrank : polarRank R.quadratic = 2 * s)
    (a : V 7) :
    certificateTransform R s a =
      -((2 ^ s : Nat) : Int) * sign (rm2Eval R a) := by
  classical
  let amplitude : Int := ((2 ^ (7 - s) : Nat) : Int)
  have hs : 2 * s ≤ 7 :=
    rank_even_bound_from_reflected_rank_q2 7 s R.quadratic (by
      simpa [polarRank, polarMatrix] using hrank)
  have hs' : s ≤ 3 := by omega
  have hampProduct : amplitude * ((2 ^ s : Nat) : Int) = 128 := by
    change ((2 ^ (7 - s) : Nat) : Int) * ((2 ^ s : Nat) : Int) = 128
    norm_cast
    rw [← pow_add, Nat.sub_add_cancel (by omega : s ≤ 7)]
    norm_num
  have hfull :
      (∑ x ∈ walshSupport R, walsh (rm2Eval R) x * character x a) =
        ∑ x : V 7, walsh (rm2Eval R) x * character x a := by
    calc
      (∑ x ∈ walshSupport R, walsh (rm2Eval R) x * character x a) =
          ∑ x : V 7,
            if walsh (rm2Eval R) x ≠ 0 then
              walsh (rm2Eval R) x * character x a
            else 0 := by
        simpa [walshSupport] using
          (Finset.sum_filter
            (fun x : V 7 => walsh (rm2Eval R) x ≠ 0)
            (fun x => walsh (rm2Eval R) x * character x a))
      _ = ∑ x : V 7, walsh (rm2Eval R) x * character x a := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : walsh (rm2Eval R) x = 0 <;> simp [hx]
  have hscaled : amplitude * certificateTransform R s a =
      -(∑ x : V 7, walsh (rm2Eval R) x * character x a) := by
    calc
      amplitude * certificateTransform R s a =
          ∑ x ∈ walshSupport R,
            amplitude * (certificateSign R s x * character a x) := by
        simp [certificateTransform, Finset.mul_sum]
      _ = ∑ x ∈ walshSupport R,
          -(walsh (rm2Eval R) x * character x a) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← mul_assoc, amplitude_mul_certificateSign R s hrank x hx]
        rw [character_comm]
        ring
      _ = -(∑ x ∈ walshSupport R,
          walsh (rm2Eval R) x * character x a) := by simp
      _ = -(∑ x : V 7, walsh (rm2Eval R) x * character x a) := by
        rw [hfull]
  have hinversion := walsh_inversion (rm2Eval R) a
  have htarget :
      amplitude * certificateTransform R s a =
        amplitude * (-((2 ^ s : Nat) : Int) * sign (rm2Eval R a)) := by
    calc
      amplitude * certificateTransform R s a =
          -(∑ x : V 7, walsh (rm2Eval R) x * character x a) := hscaled
      _ = -((2 : Int) ^ 7 * sign (rm2Eval R a)) := by rw [hinversion]
      _ = amplitude * (-((2 ^ s : Nat) : Int) * sign (rm2Eval R a)) := by
        rw [show (2 : Int) ^ 7 = 128 by norm_num, ← hampProduct]
        ring
  exact mul_left_cancel₀ (by positivity : amplitude ≠ 0) htarget

theorem certificateSign_sum
    (R : RM2 7) (s : Nat) (hrank : polarRank R.quadratic = 2 * s) :
    (∑ x ∈ walshSupport R, certificateSign R s x) =
      -((2 ^ s : Nat) : Int) := by
  simpa [certificateTransform] using certificateTransform_eq R s hrank (0 : V 7)

theorem exists_balanced_quadratic_spectrum_certificate
    (R : RM2 7) (s : Nat)
    (hrank : polarRank R.quadratic = 2 * s)
    (hbalanced : weight (rm2Eval R) = 64) :
    ∃ X : Finset (V 7), ∃ tau : V 7 -> Int,
      X.card = 2 ^ (2 * s) ∧
      0 ∉ X ∧
      (∀ x ∈ X, tau x = 1 ∨ tau x = -1) ∧
      (∑ x ∈ X, tau x) = -((2 ^ s : Nat) : Int) ∧
      ∀ a : V 7,
        (∑ x ∈ X, tau x * character a x) =
          -((2 ^ s : Nat) : Int) * sign (rm2Eval R a) := by
  classical
  refine ⟨walshSupport R, certificateSign R s,
    walshSupport_card R s hrank, ?_, ?_, certificateSign_sum R s hrank, ?_⟩
  · have hzero : walsh (rm2Eval R) (0 : V 7) = 0 := by
      rw [walsh_eq_card_sub_two_mul_weight]
      simp [hbalanced]
    simp [walshSupport, hzero]
  · intro x _
    exact certificateSign_eq_one_or_neg_one R s x
  · intro a
    exact certificateTransform_eq R s hrank a

def restrictedCharacter
    (A : Matrix (Fin 7) (Fin 7) (ZMod 2)) (a : V 7) :
    AddChar (LinearMap.range (Matrix.toLin' A)) Int where
  toFun u := character a u.1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    exact character_add_right a x.1 y.1

theorem restrictedCharacter_eq_zero_iff
    (A : Matrix (Fin 7) (Fin 7) (ZMod 2))
    (hsymm : ∀ i j, A i j = A j i) (a : V 7) :
    restrictedCharacter A a = 0 ↔ Matrix.toLin' A a = 0 := by
  classical
  constructor
  · intro hchar
    funext i
    let u : LinearMap.range (Matrix.toLin' A) :=
      ⟨Matrix.toLin' A (basisVector i), ⟨basisVector i, rfl⟩⟩
    have hone : character a (Matrix.toLin' A (basisVector i)) = 1 := by
      have h := DFunLike.congr_fun hchar u
      simpa [restrictedCharacter, u] using h
    have hdot : f2Dot a (Matrix.toLin' A (basisVector i)) = 0 :=
      (sign_eq_one_iff _).mp (by simpa [character] using hone)
    have hswap :
        f2Dot a (Matrix.toLin' A (basisVector i)) =
          f2Dot (basisVector i) (Matrix.toLin' A a) := by
      calc
        f2Dot a (Matrix.toLin' A (basisVector i)) =
            f2Dot (Matrix.toLin' A (basisVector i)) a :=
          f2Dot_comm _ _
        _ = f2Dot (basisVector i) (Matrix.toLin' A a) := by
          simpa [f2Dot] using
            (symmetric_tolin_dot_comm 7 A hsymm (basisVector i) a)
    calc
      Matrix.toLin' A a i = f2Dot (basisVector i) (Matrix.toLin' A a) := by
        symm
        exact f2Dot_basis_left i (Matrix.toLin' A a)
      _ = f2Dot a (Matrix.toLin' A (basisVector i)) := hswap.symm
      _ = 0 := hdot
  · intro ha
    ext u
    simp only [AddChar.zero_apply]
    change character a u.1 = 1
    apply (LeanCipher.BooleanWalsh.sign_eq_one_iff _).2
    have hdot := symmetric_tolin_range_kernel_dot_zero_q2
      7 A hsymm u.1 a u.2 ha
    simpa [restrictedCharacter, character, f2Dot, mul_comm] using hdot

theorem range_character_sum
    (A : Matrix (Fin 7) (Fin 7) (ZMod 2))
    (hsymm : ∀ i j, A i j = A j i)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' A)) = 6)
    (a : V 7) :
    (∑ u : LinearMap.range (Matrix.toLin' A), character a u.1) =
      if Matrix.toLin' A a = 0 then 64 else 0 := by
  classical
  rw [show (∑ u : LinearMap.range (Matrix.toLin' A), character a u.1) =
      ∑ u, restrictedCharacter A a u by rfl]
  rw [AddChar.sum_eq_ite]
  by_cases ha : Matrix.toLin' A a = 0
  · have hchar : restrictedCharacter A a = 0 :=
      (restrictedCharacter_eq_zero_iff A hsymm a).2 ha
    rw [if_pos hchar, if_pos ha]
    have hcard := card_range_tolin_prime_eq_pow_finrank 7 6 A hrank
    norm_num at hcard ⊢
    exact_mod_cast hcard
  · have hchar : restrictedCharacter A a ≠ 0 := by
      exact fun h => ha ((restrictedCharacter_eq_zero_iff A hsymm a).1 h)
    rw [if_neg hchar, if_neg ha]

private theorem support_iff_anchor_add_mem_range
    (R : RM2 7) (z : V 7) (hz : z ∈ walshSupport R) (a : V 7) :
    a ∈ walshSupport R ↔
      a + z ∈ LinearMap.range (Matrix.toLin' (polarMatrix R.quadratic)) := by
  have hzPhase : phaseWalsh R.quadratic (R.linear + z) ≠ 0 := by
    rw [← rm2_walsh_eq_phaseWalsh]
    simpa [walshSupport] using hz
  have h := upperTriangular_walshSupport_iff_anchor_range_q2
    7 R.quadratic (R.linear + z) (R.linear + a) (by
      simpa [phaseWalsh, quadraticEval, f2Dot, sign] using hzPhase)
  have hcancel : (R.linear + a) + (R.linear + z) = a + z := by
    funext i
    simp [Pi.add_apply, add_left_comm, add_comm,
      CharTwo.add_self_eq_zero]
  rw [hcancel] at h
  simpa [walshSupport, rm2_walsh_eq_phaseWalsh, phaseWalsh,
    quadraticEval, f2Dot, sign, polarMatrix] using h

theorem support_character_sum_rank_six
    (R : RM2 7)
    (hrank : polarRank R.quadratic = 6)
    (z : V 7) (hz : z ∈ walshSupport R) (a : V 7) :
    (∑ x ∈ walshSupport R, character a x) =
      if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then
        64 * character a z
      else 0 := by
  classical
  let A := polarMatrix R.quadratic
  have hsymm : ∀ i j, A i j = A j i := by
    simpa [A, polarMatrix] using
      (upper_triangular_quadratic_coeff_to_alt_matrix_valid_q2
        7 R.quadratic).2
  have hrange : Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' A)) = 6 := by
    simpa [A, polarRank] using hrank
  let e : {x : V 7 // x ∈ walshSupport R} ≃
      LinearMap.range (Matrix.toLin' A) :=
    { toFun := fun x =>
        ⟨x.1 + z, by
          simpa [A] using (support_iff_anchor_add_mem_range R z hz x.1).mp x.2⟩
      invFun := fun u =>
        ⟨u.1 + z, (support_iff_anchor_add_mem_range R z hz (u.1 + z)).mpr (by
          have hu : u.1 ∈ LinearMap.range (Matrix.toLin' A) := u.2
          simp [A, add_comm, hu])⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp [add_assoc, CharTwo.add_self_eq_zero]
      right_inv := by
        intro u
        apply Subtype.ext
        simp [add_assoc, CharTwo.add_self_eq_zero] }
  have hsubtype :
      (∑ x ∈ walshSupport R, character a x) =
        ∑ x : {x : V 7 // x ∈ walshSupport R}, character a x.1 := by
    exact Finset.sum_subtype (walshSupport R) (fun _ => Iff.rfl) (character a)
  have hreindex :
      (∑ x : {x : V 7 // x ∈ walshSupport R}, character a x.1) =
        ∑ u : LinearMap.range (Matrix.toLin' A), character a (u.1 + z) := by
    exact Fintype.sum_equiv e
      (fun x : {x : V 7 // x ∈ walshSupport R} => character a x.1)
      (fun u : LinearMap.range (Matrix.toLin' A) => character a (u.1 + z))
      (fun x => by
        simp [e, add_assoc, CharTwo.add_self_eq_zero])
  calc
    (∑ x ∈ walshSupport R, character a x) =
        ∑ u : LinearMap.range (Matrix.toLin' A), character a (u.1 + z) :=
      hsubtype.trans hreindex
    _ = (∑ u : LinearMap.range (Matrix.toLin' A), character a u.1) *
        character a z := by
      simp only [character_add_right, Finset.sum_mul]
    _ = (if Matrix.toLin' A a = 0 then 64 else 0) * character a z := by
      rw [range_character_sum A hsymm hrange a]
    _ = if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then
          64 * character a z else 0 := by
      simp [A]

def negativeWalshSet (R : RM2 7) : Finset (V 7) :=
  Finset.univ.filter fun a => walsh (rm2Eval R) a = -16

def negativeWalshTransform (R : RM2 7) (a : V 7) : Int :=
  ∑ x ∈ negativeWalshSet R, character a x

theorem rank_six_walsh_cases
    (R : RM2 7) (hrank : polarRank R.quadratic = 6) (a : V 7) :
    walsh (rm2Eval R) a = 0 ∨
      walsh (rm2Eval R) a = 16 ∨ walsh (rm2Eval R) a = -16 := by
  by_cases hzero : walsh (rm2Eval R) a = 0
  · exact Or.inl hzero
  · have habs := rm2_walsh_natAbs R 3 (by simpa using hrank) a hzero
    norm_num at habs
    rcases Int.natAbs_eq_iff.mp habs with hpos | hneg
    · exact Or.inr (Or.inl (by norm_num at hpos ⊢; exact hpos))
    · exact Or.inr (Or.inr (by norm_num at hneg ⊢; exact hneg))

theorem rank_six_walsh_indicator_identity
    (R : RM2 7) (hrank : polarRank R.quadratic = 6) (a : V 7) :
    walsh (rm2Eval R) a =
      16 * (if a ∈ walshSupport R then 1 else 0) -
        32 * (if a ∈ negativeWalshSet R then 1 else 0) := by
  rcases rank_six_walsh_cases R hrank a with hzero | hpos | hneg
  · simp [walshSupport, negativeWalshSet, hzero]
  · simp [walshSupport, negativeWalshSet, hpos]
  · simp [walshSupport, negativeWalshSet, hneg]

theorem negativeWalshTransform_rank_six
    (R : RM2 7) (hrank : polarRank R.quadratic = 6)
    (z : V 7) (hz : z ∈ walshSupport R) (a : V 7) :
    negativeWalshTransform R a =
      if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then
        32 * character a z - 4 * sign (rm2Eval R a)
      else
        -4 * sign (rm2Eval R a) := by
  classical
  let supportIndicator : V 7 -> Int := fun x =>
    if x ∈ walshSupport R then 1 else 0
  let negativeIndicator : V 7 -> Int := fun x =>
    if x ∈ negativeWalshSet R then 1 else 0
  have hsupportIndicator :
      (∑ x : V 7, supportIndicator x * character x a) =
        ∑ x ∈ walshSupport R, character x a := by
    calc
      (∑ x : V 7, supportIndicator x * character x a) =
          ∑ x : V 7,
            if x ∈ walshSupport R then character x a else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ walshSupport R <;> simp [supportIndicator, hx]
      _ = ∑ x ∈ walshSupport R, character x a := by
        symm
        simpa [walshSupport] using (Finset.sum_filter (s := Finset.univ)
          (fun x : V 7 => walsh (rm2Eval R) x ≠ 0)
          (fun x : V 7 => character x a)
        )
  have hnegativeIndicator :
      (∑ x : V 7, negativeIndicator x * character x a) =
        negativeWalshTransform R a := by
    calc
      (∑ x : V 7, negativeIndicator x * character x a) =
          ∑ x : V 7,
            if x ∈ negativeWalshSet R then character x a else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ negativeWalshSet R <;> simp [negativeIndicator, hx]
      _ = ∑ x ∈ negativeWalshSet R, character x a := by
        symm
        simpa [negativeWalshSet] using (Finset.sum_filter (s := Finset.univ)
          (fun x : V 7 => walsh (rm2Eval R) x = -16)
          (fun x : V 7 => character x a)
        )
      _ = negativeWalshTransform R a := by
        rw [negativeWalshTransform]
        apply Finset.sum_congr rfl
        intro x _
        exact character_comm x a
  have hsumDecomposition :
      (∑ x : V 7, walsh (rm2Eval R) x * character x a) =
        16 * (∑ x ∈ walshSupport R, character x a) -
          32 * negativeWalshTransform R a := by
    calc
      (∑ x : V 7, walsh (rm2Eval R) x * character x a) =
          ∑ x : V 7,
            (16 * supportIndicator x - 32 * negativeIndicator x) * character x a := by
        apply Finset.sum_congr rfl
        intro x _
        rw [rank_six_walsh_indicator_identity R hrank x]
      _ = 16 * (∑ x : V 7, supportIndicator x * character x a) -
          32 * (∑ x : V 7, negativeIndicator x * character x a) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = 16 * (∑ x ∈ walshSupport R, character x a) -
          32 * negativeWalshTransform R a := by
        rw [hsupportIndicator, hnegativeIndicator]
  have hinversion :
      (∑ x : V 7, walsh (rm2Eval R) x * character x a) =
        128 * sign (rm2Eval R a) := by
    simpa using walsh_inversion (rm2Eval R) a
  have hsupport := support_character_sum_rank_six R hrank z hz a
  rw [show (∑ x ∈ walshSupport R, character x a) =
      ∑ x ∈ walshSupport R, character a x by
        apply Finset.sum_congr rfl
        intro x _
        exact character_comm x a] at hsumDecomposition
  rw [hsupport] at hsumDecomposition
  by_cases hkernel : Matrix.toLin' (polarMatrix R.quadratic) a = 0
  · rw [if_pos hkernel] at hsumDecomposition ⊢
    rw [hinversion] at hsumDecomposition
    omega
  · rw [if_neg hkernel] at hsumDecomposition ⊢
    rw [hinversion] at hsumDecomposition
    omega

theorem exists_rank_six_negative_walsh_certificate
    (R : RM2 7) (hrank : polarRank R.quadratic = 6) :
    ∃ z : V 7, z ∈ walshSupport R ∧
      (negativeWalshSet R).card = 28 ∧
      ∀ a : V 7,
        negativeWalshTransform R a =
          if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then
            32 * character a z - 4 * sign (rm2Eval R a)
          else
            -4 * sign (rm2Eval R a) := by
  classical
  have hsupportCard : (walshSupport R).card = 64 := by
    simpa using walshSupport_card R 3 (by simpa using hrank)
  obtain ⟨z, hz⟩ : ∃ z, z ∈ walshSupport R := by
    exact Finset.card_pos.mp (by omega : 0 < (walshSupport R).card)
  refine ⟨z, hz, ?_, negativeWalshTransform_rank_six R hrank z hz⟩
  have hzero := negativeWalshTransform_rank_six R hrank z hz (0 : V 7)
  have htransformCard : negativeWalshTransform R 0 =
      ((negativeWalshSet R).card : Int) := by
    simp [negativeWalshTransform]
  rw [htransformCard] at hzero
  norm_num [rm2Eval_zero] at hzero
  exact_mod_cast hzero

def polarKernelSet (R : RM2 7) : Finset (V 7) :=
  Finset.univ.filter fun a =>
    Matrix.toLin' (polarMatrix R.quadratic) a = 0

theorem polarKernelSet_card_rank_six
    (R : RM2 7) (hrank : polarRank R.quadratic = 6) :
    (polarKernelSet R).card = 2 := by
  classical
  let A := polarMatrix R.quadratic
  have hrange : Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' A)) = 6 := by
    simpa [A, polarRank] using hrank
  have hdim := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have hdomain : Module.finrank (ZMod 2) (V 7) = 7 := f2Vec_finrank 7
  rw [hrange, hdomain] at hdim
  have hkernelRank :
      Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' A)) = 1 := by
    omega
  have hkernelCard :
      Fintype.card {a : V 7 // Matrix.toLin' A a = 0} = 2 := by
    rw [matrix_tolin_kernel_subtype_card_eq_two_pow_finrank, hkernelRank]
    norm_num
  calc
    (polarKernelSet R).card =
        Fintype.card {a : V 7 // Matrix.toLin' A a = 0} := by
      symm
      exact Fintype.card_ofFinset
        (p := {a : V 7 | Matrix.toLin' A a = 0})
        (polarKernelSet R) (fun a => by simp [polarKernelSet, A])
    _ = 2 := hkernelCard

private theorem walsh_zero_eq_of_weight
    (R : RM2 7) (w : Nat) (hweight : weight (rm2Eval R) = w) :
    walsh (rm2Eval R) (0 : V 7) = 128 - 2 * (w : Int) := by
  rw [walsh_eq_card_sub_two_mul_weight]
  simp [hweight]

theorem weight_56_zero_mem_walshSupport
    (R : RM2 7) (hweight : weight (rm2Eval R) = 56) :
    (0 : V 7) ∈ walshSupport R := by
  have hwalsh : walsh (rm2Eval R) (0 : V 7) = 16 := by
    simpa using walsh_zero_eq_of_weight R 56 hweight
  simp [walshSupport, hwalsh]

theorem weight_56_vanishes_on_polarKernel
    (R : RM2 7) (hweight : weight (rm2Eval R) = 56)
    (a : V 7)
    (ha : Matrix.toLin' (polarMatrix R.quadratic) a = 0) :
    rm2Eval R a = 0 := by
  have hwalsh : walsh (rm2Eval R) (0 : V 7) = 16 := by
    simpa using walsh_zero_eq_of_weight R 56 hweight
  have hphase : phaseWalsh R.quadratic R.linear ≠ 0 := by
    have hbridge := rm2_walsh_eq_phaseWalsh R (0 : V 7)
    simp only [add_zero] at hbridge
    rw [← hbridge]
    omega
  have hvanish := (phaseWalsh_ne_zero_iff_kernel R.quadratic R.linear).1
    hphase a ha
  simpa [rm2Eval] using hvanish

theorem weight_56_negative_walsh_certificate
    (R : RM2 7) (hrank : polarRank R.quadratic = 6)
    (hweight : weight (rm2Eval R) = 56) :
    (negativeWalshSet R).card = 28 ∧
      ∀ a : V 7,
        negativeWalshTransform R a =
          if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then
            28
          else
            -4 * sign (rm2Eval R a) := by
  have hz : (0 : V 7) ∈ walshSupport R :=
    weight_56_zero_mem_walshSupport R hweight
  have hcard := (exists_rank_six_negative_walsh_certificate R hrank).choose_spec.2.1
  refine ⟨hcard, ?_⟩
  intro a
  have htransform := negativeWalshTransform_rank_six R hrank (0 : V 7) hz a
  by_cases ha : Matrix.toLin' (polarMatrix R.quadratic) a = 0
  · rw [if_pos ha] at htransform ⊢
    have hRa := weight_56_vanishes_on_polarKernel R hweight a ha
    simpa [hRa] using htransform
  · rw [if_neg ha] at htransform ⊢
    exact htransform

private theorem balanced_zero_not_mem_walshSupport
    (R : RM2 7) (hweight : weight (rm2Eval R) = 64) :
    (0 : V 7) ∉ walshSupport R := by
  have hwalsh : walsh (rm2Eval R) (0 : V 7) = 0 := by
    simpa using walsh_zero_eq_of_weight R 64 hweight
  simp [walshSupport, hwalsh]

theorem balanced_rank_six_polarKernel_value
    (R : RM2 7) (hrank : polarRank R.quadratic = 6)
    (hweight : weight (rm2Eval R) = 64)
    (a : V 7)
    (ha : Matrix.toLin' (polarMatrix R.quadratic) a = 0) :
    rm2Eval R a = if a = 0 then 0 else 1 := by
  classical
  by_cases ha0 : a = 0
  · subst a
    simp
  · rw [if_neg ha0]
    apply zmod2_eq_one_of_ne_zero
    intro hRa
    have hkernelCard := polarKernelSet_card_rank_six R hrank
    have hpairSubset : ({0, a} : Finset (V 7)) ⊆ polarKernelSet R := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · simp [polarKernelSet]
      · simpa [polarKernelSet] using ha
    have hpairCard : ({0, a} : Finset (V 7)).card = 2 := by
      exact Finset.card_pair (Ne.symm ha0)
    have hpairEq : ({0, a} : Finset (V 7)) = polarKernelSet R :=
      Finset.eq_of_subset_of_card_le hpairSubset (by
        rw [hkernelCard, hpairCard])
    have hvanishAll : ∀ y : V 7,
        Matrix.toLin' (polarMatrix R.quadratic) y = 0 ->
          quadraticEval R.quadratic y + f2Dot R.linear y = 0 := by
      intro y hy
      have hyMem : y ∈ polarKernelSet R := by
        simpa [polarKernelSet] using hy
      rw [← hpairEq] at hyMem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyMem
      rcases hyMem with rfl | rfl
      · simp [quadraticEval, f2Dot]
      · simpa [rm2Eval] using hRa
    have hphaseNonzero : phaseWalsh R.quadratic R.linear ≠ 0 :=
      (phaseWalsh_ne_zero_iff_kernel R.quadratic R.linear).2 hvanishAll
    have hwalshZero : walsh (rm2Eval R) (0 : V 7) = 0 := by
      simpa using walsh_zero_eq_of_weight R 64 hweight
    have hbridge := rm2_walsh_eq_phaseWalsh R (0 : V 7)
    simp only [add_zero] at hbridge
    exact hphaseNonzero (hbridge ▸ hwalshZero)

theorem balanced_rank_six_anchor_character
    (R : RM2 7) (hrank : polarRank R.quadratic = 6)
    (hweight : weight (rm2Eval R) = 64)
    (z : V 7) (hz : z ∈ walshSupport R)
    (a : V 7)
    (ha : Matrix.toLin' (polarMatrix R.quadratic) a = 0)
    (ha0 : a ≠ 0) :
    character a z = -1 := by
  have hzPhase : phaseWalsh R.quadratic (R.linear + z) ≠ 0 := by
    rw [← rm2_walsh_eq_phaseWalsh]
    simpa [walshSupport] using hz
  have hphase := (phaseWalsh_ne_zero_iff_kernel
    R.quadratic (R.linear + z)).1 hzPhase a ha
  have hRa : rm2Eval R a = 1 := by
    simpa [ha0] using
      balanced_rank_six_polarKernel_value R hrank hweight a ha
  have hsplit : rm2Eval R a + f2Dot z a = 0 := by
    simpa [rm2Eval, f2Dot_add_left, add_assoc, add_left_comm, add_comm] using hphase
  have hdot : f2Dot z a = 1 := by
    rw [hRa] at hsplit
    rcases zmod2_eq_zero_or_one (f2Dot z a) with h | h
    · rw [h] at hsplit
      norm_num at hsplit
    · exact h
  rw [character, f2Dot_comm, hdot]
  exact sign_one

theorem balanced_rank_six_negative_walsh_certificate
    (R : RM2 7) (hrank : polarRank R.quadratic = 6)
    (hweight : weight (rm2Eval R) = 64) :
    ∃ z : V 7, z ∈ walshSupport R ∧
      (negativeWalshSet R).card = 28 ∧
      ∀ a : V 7,
        negativeWalshTransform R a =
          if Matrix.toLin' (polarMatrix R.quadratic) a = 0 then
            if a = 0 then 28 else -28
          else
            -4 * sign (rm2Eval R a) := by
  obtain ⟨z, hz, hcard, htransform⟩ :=
    exists_rank_six_negative_walsh_certificate R hrank
  refine ⟨z, hz, hcard, ?_⟩
  intro a
  specialize htransform a
  by_cases ha : Matrix.toLin' (polarMatrix R.quadratic) a = 0
  · rw [if_pos ha] at htransform ⊢
    by_cases ha0 : a = 0
    · subst a
      norm_num [rm2Eval_zero] at htransform ⊢
      exact htransform
    · rw [if_neg ha0]
      have hcharacter := balanced_rank_six_anchor_character
        R hrank hweight z hz a ha ha0
      have hRa := balanced_rank_six_polarKernel_value R hrank hweight a ha
      simp only [if_neg ha0] at hRa
      simpa [hcharacter, hRa] using htransform
  · rw [if_neg ha] at htransform ⊢
    exact htransform

end LeanCipher.BalancedEightQuadratic

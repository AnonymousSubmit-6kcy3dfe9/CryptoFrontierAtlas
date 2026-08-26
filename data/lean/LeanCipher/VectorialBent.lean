import LeanCipher.BooleanWalsh
import Mathlib

open scoped BigOperators

namespace LeanCipher.VectorialBent

open LeanCipher.BooleanWalsh

/-! Linear-algebra and fibre-count consequences of vectorial bentness. -/

def dotRight (y : V n) : V n →ₗ[ZMod 2] ZMod 2 where
  toFun := fun x => f2Dot x y
  map_add' := f2Dot_add_left (x := y)
  map_smul' := by
    intro c x
    simp [f2Dot, Finset.mul_sum, mul_assoc]

@[simp]
theorem dotRight_apply (y x : V n) : dotRight y x = f2Dot x y := rfl

theorem dotRight_ne_zero {y : V n} (hy : y ≠ 0) : dotRight y ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_ne_zero_coordinate hy
  intro h
  have hi' := DFunLike.congr_fun h (basisVector i)
  simp only [dotRight_apply, f2Dot_basis_left, LinearMap.zero_apply] at hi'
  exact hi hi'

theorem dotRight_surjective {y : V n} (hy : y ≠ 0) :
    Function.Surjective (dotRight y) := by
  simpa only [dotRight_apply] using f2Dot_right_surjective hy

theorem dotRight_ker_finrank {y : V n} (hy : y ≠ 0) :
    Module.finrank (ZMod 2) (dotRight y).ker = n - 1 := by
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero (dotRight_ne_zero hy)
  rw [f2Vec_finrank] at hdim
  omega

theorem dotRight_ker_card {y : V n} (hy : y ≠ 0) :
    Nat.card (dotRight y).ker = 2 ^ (n - 1) := by
  rw [@Module.natCard_eq_pow_finrank (ZMod 2) (dotRight y).ker,
    dotRight_ker_finrank hy]
  norm_num

def IsBent {k : Nat} (f : V (2 * k) -> ZMod 2) : Prop :=
  forall a, |walsh f a| = (2 : Int) ^ k

def IsVectorialBent {k r : Nat} (G : V (2 * k) -> V r) : Prop :=
  forall b, b ≠ 0 -> IsBent (component G b)

theorem IsVectorialBent.component_isBent
    {G : V (2 * k) -> V r} (hG : IsVectorialBent G) {b : V r} (hb : b ≠ 0) :
    IsBent (component G b) :=
  hG b hb

def spectrumSign (f : V n -> ZMod 2) (a : V n) : Int :=
  if 0 <= walsh f a then 1 else -1

theorem spectrumSign_eq_one_or_neg_one (f : V n -> ZMod 2) (a : V n) :
    spectrumSign f a = 1 \/ spectrumSign f a = -1 := by
  simp only [spectrumSign]
  split_ifs <;> simp

theorem spectrumSign_odd (f : V n -> ZMod 2) (a : V n) :
    Odd (spectrumSign f a) := by
  rcases spectrumSign_eq_one_or_neg_one f a with h | h <;> rw [h] <;> norm_num [Odd]

theorem IsBent.walsh_eq_scale_mul_spectrumSign
    {f : V (2 * k) -> ZMod 2} (hf : IsBent f) (a : V (2 * k)) :
    walsh f a = (2 : Int) ^ k * spectrumSign f a := by
  have hAbs := hf a
  by_cases hNonneg : 0 <= walsh f a
  · rw [abs_of_nonneg hNonneg] at hAbs
    simp [spectrumSign, hAbs]
  · have hNeg : walsh f a < 0 := lt_of_not_ge hNonneg
    rw [abs_of_neg hNeg] at hAbs
    simp [spectrumSign, hNonneg]
    linarith

def outputSum (F : V n -> V m) : V m :=
  ∑ x, F x

theorem component_sum_eq_dot_outputSum (F : V n -> V m) (b : V m) :
    (∑ x, component F b x) = f2Dot b (outputSum F) := by
  simp only [component, outputSum, f2Dot]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_apply]
  exact (Finset.mul_sum _ _ _).symm

theorem component_weight_cast (F : V n -> V m) (b : V m) :
    (weight (component F b) : ZMod 2) = f2Dot b (outputSum F) := by
  rw [weight_cast_zmod2, component_sum_eq_dot_outputSum]

theorem component_weight_even_iff (F : V n -> V m) (b : V m) :
    Even (weight (component F b)) <-> f2Dot b (outputSum F) = 0 := by
  rw [weight_even_iff_sum_eq_zero, component_sum_eq_dot_outputSum]

def fibreCard (G : V n -> V r) (y : V r) : Nat :=
  Fintype.card {x : V n // G x = y}

theorem walsh_component_zero_eq_fibre_transform
    (G : V n -> V r) (b : V r) :
    walsh (component G b) 0 =
      hadamardTransform (fun b y : V r => character b y)
        (fun y => (fibreCard G y : Int)) b := by
  classical
  rw [show walsh (component G b) 0 = ∑ x, character b (G x) by
    apply Finset.sum_congr rfl
    intro x _
    simp [component, character]]
  rw [show (∑ x, character b (G x)) =
      ∑ y : V r, ∑ x : {x : V n // G x = y}, character b (G x) by
    exact (Fintype.sum_fiberwise G (fun x => character b (G x))).symm]
  apply Finset.sum_congr rfl
  intro y _
  change (∑ x : {x : V n // G x = y}, character b (G x)) =
    character b y * (fibreCard G y : Int)
  calc
    (∑ x : {x : V n // G x = y}, character b (G x)) =
        ∑ _x : {x : V n // G x = y}, character b y := by
          apply Finset.sum_congr rfl
          intro x _
          rw [x.property]
    _ = character b y * (fibreCard G y : Int) := by
      simp [fibreCard, mul_comm]

theorem output_character_fibre_inversion (G : V n -> V r) (y : V r) :
    (∑ b, walsh (component G b) 0 * character b y) =
      (2 : Int) ^ r * (fibreCard G y : Int) := by
  calc
    (∑ b, walsh (component G b) 0 * character b y) =
        ∑ b, hadamardTransform (fun b y : V r => character b y)
          (fun y => (fibreCard G y : Int)) b * character b y := by
            apply Finset.sum_congr rfl
            intro b _
            rw [walsh_component_zero_eq_fibre_transform]
    _ = (2 : Int) ^ r * (fibreCard G y : Int) :=
      hadamard_inversion _ _ _ character_columns_orthogonal y

@[simp]
theorem component_zero (G : V n -> V r) :
    component G 0 = fun _ => 0 := by
  funext x
  simp [component]

@[simp]
theorem walsh_zero_function_at_zero (n : Nat) :
    walsh (fun _ : V n => (0 : ZMod 2)) 0 = (2 : Int) ^ n := by
  simp [walsh]

def bentFibreCorrection {k r : Nat} (G : V (2 * k) -> V r) (y : V r) : Int :=
  ∑ b ∈ (Finset.univ : Finset (V r)).erase 0,
    spectrumSign (component G b) 0 * character b y

theorem bent_fibre_equation
    {G : V (2 * k) -> V r} (hG : IsVectorialBent G) (y : V r) :
    (2 : Int) ^ r * (fibreCard G y : Int) =
      (2 : Int) ^ (2 * k) + (2 : Int) ^ k * bentFibreCorrection G y := by
  classical
  let term : V r -> Int := fun b => walsh (component G b) 0 * character b y
  have hSplit :
      (∑ b : V r, term b) =
        term 0 + ∑ b ∈ (Finset.univ : Finset (V r)).erase 0, term b := by
    rw [add_comm]
    exact (Finset.sum_erase_add (Finset.univ : Finset (V r)) term
      (Finset.mem_univ 0)).symm
  calc
    (2 : Int) ^ r * (fibreCard G y : Int) = ∑ b : V r, term b := by
      exact (output_character_fibre_inversion G y).symm
    _ = term 0 + ∑ b ∈ (Finset.univ : Finset (V r)).erase 0, term b := hSplit
    _ = (2 : Int) ^ (2 * k) +
        ∑ b ∈ (Finset.univ : Finset (V r)).erase 0,
          ((2 : Int) ^ k * spectrumSign (component G b) 0) * character b y := by
      congr 1
      · dsimp [term]
        simpa only [component_zero, character_zero_left, mul_one] using
          walsh_zero_function_at_zero (2 * k)
      · apply Finset.sum_congr rfl
        intro b hb
        dsimp [term]
        rw [(hG b (Finset.ne_of_mem_erase hb)).walsh_eq_scale_mul_spectrumSign]
    _ = (2 : Int) ^ (2 * k) + (2 : Int) ^ k * bentFibreCorrection G y := by
      simp only [bentFibreCorrection]
      rw [Finset.mul_sum]
      apply congrArg ((2 : Int) ^ (2 * k) + ·)
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem odd_finset_sum_of_odd_card
    {A : Type*} [DecidableEq A] (s : Finset A) (f : A -> Int)
    (hf : forall x, x ∈ s -> Odd (f x)) (hs : Odd s.card) :
    Odd (∑ x ∈ s, f x) := by
  rw [Int.odd_iff]
  have hmod : (∑ x ∈ s, f x) ≡ (s.card : Int) [ZMOD 2] := by
    have hterms : forall x, x ∈ s -> f x ≡ (1 : Int) [ZMOD 2] := by
      intro x hx
      change f x % 2 = (1 : Int) % 2
      rw [Int.odd_iff.mp (hf x hx)]
      norm_num
    simpa using Int.ModEq.sum hterms
  calc
    (∑ x ∈ s, f x) % 2 = (s.card : Int) % 2 := hmod
    _ = ((s.card % 2 : Nat) : Int) := (Int.natCast_emod s.card 2).symm
    _ = 1 := by rw [Nat.odd_iff.mp hs]; norm_num

theorem character_odd (b y : V r) : Odd (character b y) := by
  rcases zmod2_eq_zero_or_one (f2Dot b y) with h | h <;>
    simp [character, sign, h]

theorem erase_zero_card (r : Nat) :
    ((Finset.univ : Finset (V r)).erase 0).card = 2 ^ r - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, f2Vec_card]

theorem erase_zero_card_odd {r : Nat} (hr : 0 < r) :
    Odd ((Finset.univ : Finset (V r)).erase 0).card := by
  rw [erase_zero_card]
  refine ⟨2 ^ (r - 1) - 1, ?_⟩
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [show r = 1 + (r - 1) by omega, pow_add]
    norm_num
  have hpositive : 0 < 2 ^ (r - 1) := pow_pos (by omega) _
  omega

theorem bentFibreCorrection_odd
    {G : V (2 * k) -> V r} (hr : 0 < r) (y : V r) :
    Odd (bentFibreCorrection G y) := by
  classical
  apply odd_finset_sum_of_odd_card
  · intro b _
    exact (spectrumSign_odd (component G b) 0).mul (character_odd b y)
  · exact erase_zero_card_odd hr

theorem int_two_pow_even {n : Nat} (hn : 0 < n) : Even ((2 : Int) ^ n) := by
  refine ⟨(2 : Int) ^ (n - 1), ?_⟩
  rw [show n = 1 + (n - 1) by omega, pow_add]
  norm_num
  ring

theorem nyberg_bound
    {G : V (2 * k) -> V r} (hk : 0 < k) (hG : IsVectorialBent G) : r <= k := by
  by_contra hle
  have hkr : k < r := Nat.lt_of_not_ge hle
  have hr : 0 < r := lt_trans hk hkr
  have hdiff : 0 < r - k := by omega
  have heq := bent_fibre_equation hG (0 : V r)
  have hrPow : (2 : Int) ^ r = (2 : Int) ^ k * (2 : Int) ^ (r - k) := by
    calc
      (2 : Int) ^ r = (2 : Int) ^ (k + (r - k)) := by congr 1; omega
      _ = (2 : Int) ^ k * (2 : Int) ^ (r - k) := pow_add _ _ _
  have hkPow : (2 : Int) ^ (2 * k) = (2 : Int) ^ k * (2 : Int) ^ k := by
    rw [show 2 * k = k + k by omega, pow_add]
  rw [hrPow, hkPow] at heq
  have hfactored :
      (2 : Int) ^ k * ((2 : Int) ^ (r - k) * (fibreCard G 0 : Int)) =
        (2 : Int) ^ k * ((2 : Int) ^ k + bentFibreCorrection G 0) := by
    nlinarith
  have hcancel :
      (2 : Int) ^ (r - k) * (fibreCard G 0 : Int) =
        (2 : Int) ^ k + bentFibreCorrection G 0 := by
    exact mul_left_cancel₀ (pow_ne_zero k (by norm_num : (2 : Int) ≠ 0)) hfactored
  have hleftEven :
      Even ((2 : Int) ^ (r - k) * (fibreCard G 0 : Int)) :=
    (int_two_pow_even hdiff).mul_right _
  have hrightOdd : Odd ((2 : Int) ^ k + bentFibreCorrection G 0) :=
    (int_two_pow_even hk).add_odd (bentFibreCorrection_odd hr 0)
  exact (Int.not_even_iff_odd.mpr hrightOdd) (hcancel ▸ hleftEven)

theorem maximal_vectorial_bent_fibre_odd
    {G : V (2 * k) -> V k} (hk : 0 < k) (hG : IsVectorialBent G) (y : V k) :
    Odd (fibreCard G y) := by
  have heq := bent_fibre_equation hG y
  have hkPow : (2 : Int) ^ (2 * k) = (2 : Int) ^ k * (2 : Int) ^ k := by
    rw [show 2 * k = k + k by omega, pow_add]
  rw [hkPow] at heq
  have hfactored :
      (2 : Int) ^ k * (fibreCard G y : Int) =
        (2 : Int) ^ k * ((2 : Int) ^ k + bentFibreCorrection G y) := by
    nlinarith
  have hcard :
      (fibreCard G y : Int) = (2 : Int) ^ k + bentFibreCorrection G y := by
    exact mul_left_cancel₀ (pow_ne_zero k (by norm_num : (2 : Int) ≠ 0)) hfactored
  have hoddInt : Odd (fibreCard G y : Int) := by
    rw [hcard]
    exact (int_two_pow_even hk).add_odd (bentFibreCorrection_odd hk y)
  exact_mod_cast hoddInt

theorem isBent_of_weight_even_of_walsh_ceiling
    {f : V (2 * k) -> ZMod 2} (hk : 2 <= k)
    (hEven : Even (weight f))
    (hCeiling : forall a, |walsh f a| <= (2 : Int) ^ k + 2) :
    IsBent f := by
  have hqNonneg : 0 <= (2 : Int) ^ k := pow_nonneg (by norm_num) _
  have hqFour : exists t : Int, (2 : Int) ^ k = 4 * t := by
    refine ⟨(2 : Int) ^ (k - 2), ?_⟩
    rw [show k = 2 + (k - 2) by omega, pow_add]
    norm_num
  have hAbsBound : forall a, |walsh f a| <= (2 : Int) ^ k := by
    intro a
    have hFour : (4 : Int) ∣ walsh f a :=
      four_dvd_walsh_of_weight_even f a (by omega) hEven
    have hFourAbs : (4 : Int) ∣ |walsh f a| := (dvd_abs 4 (walsh f a)).mpr hFour
    obtain ⟨u, hu⟩ := hFourAbs
    obtain ⟨t, ht⟩ := hqFour
    by_contra hle
    have hLower : (2 : Int) ^ k < |walsh f a| := lt_of_not_ge hle
    have hUpper := hCeiling a
    omega
  have hSquareBound : forall a, walsh f a ^ 2 <= ((2 : Int) ^ k) ^ 2 := by
    intro a
    have ha := hAbsBound a
    nlinarith [sq_abs (walsh f a), abs_nonneg (walsh f a)]
  have hQSquare : ((2 : Int) ^ k) ^ 2 = (2 : Int) ^ (2 * k) := by
    calc
      ((2 : Int) ^ k) ^ 2 = (2 : Int) ^ (k * 2) := (pow_mul _ _ _).symm
      _ = (2 : Int) ^ (2 * k) := by congr 1; omega
  have hSumEquality :
      (∑ a : V (2 * k), walsh f a ^ 2) =
        ∑ _a : V (2 * k), ((2 : Int) ^ k) ^ 2 := by
    rw [walsh_parseval]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [f2Vec_card, hQSquare]
    push_cast
    ring
  have hAllSquares : forall a, walsh f a ^ 2 = ((2 : Int) ^ k) ^ 2 := by
    have hPointwise :=
      (Finset.sum_eq_sum_iff_of_le
        (s := (Finset.univ : Finset (V (2 * k))))
        (f := fun a => walsh f a ^ 2)
        (g := fun _a => ((2 : Int) ^ k) ^ 2)
        (fun a _ => hSquareBound a)).mp hSumEquality
    intro a
    exact hPointwise a (Finset.mem_univ a)
  intro a
  have hsq := hAllSquares a
  nlinarith [sq_abs (walsh f a), abs_nonneg (walsh f a)]

theorem component_isBent_of_even_weight_ceiling
    (F : V (2 * k) -> V m) (b : V m) (hk : 2 <= k)
    (hEven : Even (weight (component F b)))
    (hCeiling : forall a, |walsh (component F b) a| <= (2 : Int) ^ k + 2) :
    IsBent (component F b) :=
  isBent_of_weight_even_of_walsh_ceiling hk hEven hCeiling

theorem kernel_component_isBent_of_walsh_ceiling
    (F : V (2 * k) -> V m) (b : V m) (hk : 2 <= k)
    (hb : f2Dot b (outputSum F) = 0)
    (hCeiling : forall a, |walsh (component F b) a| <= (2 : Int) ^ k + 2) :
    IsBent (component F b) := by
  apply component_isBent_of_even_weight_ceiling F b hk
  · exact (component_weight_even_iff F b).mpr hb
  · exact hCeiling

end LeanCipher.VectorialBent

import LeanCipher.BooleanWalsh
import LeanCipher.VectorialBent
import CryptoFrontierAtlas.VectorialNonlinearity

open scoped BigOperators

namespace LeanCipher.VectorialCritical

open LeanCipher.BooleanWalsh

def outputMoment (G : V n -> V m) (h : V n -> ZMod 2) : V m :=
  fun i => ∑ x, h x * G x i

def inputMoment (h : V n -> ZMod 2) : V n :=
  fun i => ∑ x, h x * x i

def bitValue (b : ZMod 2) : Int :=
  if b = 0 then 0 else 1

theorem bitValue_add (b c : ZMod 2) :
    bitValue (b + c) = bitValue b + bitValue c - 2 * bitValue (b * c) := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;>
      simp [bitValue, CharTwo.add_self_eq_zero]

theorem weight_eq_sum_bitValue (f : V n -> ZMod 2) :
    (weight f : Int) = ∑ x, bitValue (f x) := by
  simpa [weight, bitValue] using
    (Finset.sum_boole (R := Int) (fun x : V n => f x ≠ 0)
      (Finset.univ : Finset (V n))).symm

theorem sum_mul_f2Dot
    (G : V n -> V m) (h : V n -> ZMod 2) (u : V m) :
    (∑ x, h x * f2Dot u (G x)) = f2Dot u (outputMoment G h) := by
  simp only [f2Dot, outputMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem sum_mul_inputDot (h : V n -> ZMod 2) (a : V n) :
    (∑ x, h x * f2Dot a x) = f2Dot a (inputMoment h) := by
  simpa [inputMoment] using
    (sum_mul_f2Dot (fun x : V n => x) h a)

theorem weight_add_eq
    (f g : V n -> ZMod 2) :
    (weight (fun x => f x + g x) : Int) =
      (weight f : Int) + (weight g : Int) -
        2 * (weight (fun x => f x * g x) : Int) := by
  simp_rw [weight_eq_sum_bitValue]
  calc
    (∑ x, bitValue (f x + g x)) =
        ∑ x, (bitValue (f x) + bitValue (g x) -
          2 * bitValue (f x * g x)) := by
            apply Finset.sum_congr rfl
            intro x _
            exact bitValue_add (f x) (g x)
    _ = (∑ x, bitValue (f x)) + (∑ x, bitValue (g x)) -
        2 * ∑ x, bitValue (f x * g x) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]

theorem product_weight_cast
    (G : V n -> V m) (h : V n -> ZMod 2) (u : V m) (a : V n) :
    (weight (fun x => h x * (component G u x + f2Dot a x)) : ZMod 2) =
      f2Dot u (outputMoment G h) + f2Dot a (inputMoment h) := by
  rw [weight_cast_zmod2]
  simp only [component_apply, mul_add, Finset.sum_add_distrib]
  rw [sum_mul_f2Dot, sum_mul_inputDot]

def halfWalsh (f : V n -> ZMod 2) (a : V n) : Int :=
  (2 : Int) ^ (n - 1) -
    (weight (fun x => f x + f2Dot a x) : Int)

theorem two_mul_halfWalsh (f : V n -> ZMod 2) (a : V n) (hn : 1 <= n) :
    2 * halfWalsh f a = walsh f a := by
  rw [walsh_eq_card_sub_two_mul_weight]
  simp only [halfWalsh]
  have hpow : (2 : Int) ^ n = 2 * (2 : Int) ^ (n - 1) := by
    calc
      (2 : Int) ^ n = 2 ^ (1 + (n - 1)) := by congr 1; omega
      _ = 2 * 2 ^ (n - 1) := by rw [pow_add]; norm_num
  rw [hpow]
  ring

theorem exists_sign_decomposition_of_odd (w : Nat) (hw : Odd w) :
    exists gamma d : Int,
      (gamma = 1 ∨ gamma = -1) ∧ -(w : Int) = gamma + 4 * d := by
  rcases hw with ⟨t, ht⟩
  by_cases hte : Even t
  · rcases hte with ⟨s, hs⟩
    refine ⟨-1, -(s : Int), Or.inr rfl, ?_⟩
    norm_cast at ht hs ⊢
    omega
  · have hto : Odd t := Nat.not_even_iff_odd.mp hte
    rcases hto with ⟨s, hs⟩
    refine ⟨1, -(s : Int) - 1, Or.inl rfl, ?_⟩
    norm_cast at ht hs ⊢
    omega

theorem sign_eq_one_or_neg_one (b : ZMod 2) : sign b = 1 ∨ sign b = -1 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp

theorem gamma_sq {gamma : Int} (hgamma : gamma = 1 ∨ gamma = -1) :
    gamma ^ 2 = 1 := by
  rcases hgamma with rfl | rfl <;> norm_num

theorem four_dvd_weight_component_add_linear
    (k : Nat) (hk : 3 <= k) (G : V (2 * k) -> V k)
    (hBent : forall u, u ≠ 0 -> forall a,
      |walsh (component G u) a| = (2 : Int) ^ k)
    (u : V k) (a : V (2 * k)) :
    4 ∣ weight (fun x => component G u x + f2Dot a x) := by
  by_cases hu : u = 0
  · subst u
    simp only [component_zero, Pi.zero_apply, zero_add]
    by_cases ha : a = 0
    · subst a
      simp [weight]
    · rw [linear_weight a ha]
      refine ⟨2 ^ (2 * k - 3), ?_⟩
      rw [show 2 * k - 1 = 2 + (2 * k - 3) by omega, pow_add]
      norm_num
  · have hAbs := hBent u hu a
    have hWalsh := walsh_eq_card_sub_two_mul_weight (component G u) a
    have hN : (2 : Int) ^ (2 * k) =
        8 * (2 : Int) ^ (2 * k - 3) := by
      rw [show 2 * k = 3 + (2 * k - 3) by omega, pow_add]
      norm_num
    have hq : (2 : Int) ^ k = 8 * (2 : Int) ^ (k - 3) := by
      rw [show k = 3 + (k - 3) by omega, pow_add]
      norm_num
    by_cases hnonneg : 0 <= walsh (component G u) a
    · rw [abs_of_nonneg hnonneg] at hAbs
      have hWeight :
          (weight (fun x => component G u x + f2Dot a x) : Int) =
            4 * ((2 : Int) ^ (2 * k - 3) - (2 : Int) ^ (k - 3)) := by
        rw [hN] at hWalsh
        rw [hq] at hAbs
        nlinarith
      have hDivInt : (4 : Int) ∣
          (weight (fun x => component G u x + f2Dot a x) : Int) :=
        ⟨(2 : Int) ^ (2 * k - 3) - (2 : Int) ^ (k - 3), hWeight⟩
      exact_mod_cast hDivInt
    · have hnonpos : walsh (component G u) a <= 0 := le_of_not_ge hnonneg
      rw [abs_of_nonpos hnonpos] at hAbs
      have hWeight :
          (weight (fun x => component G u x + f2Dot a x) : Int) =
            4 * ((2 : Int) ^ (2 * k - 3) + (2 : Int) ^ (k - 3)) := by
        rw [hN] at hWalsh
        rw [hq] at hAbs
        nlinarith
      have hDivInt : (4 : Int) ∣
          (weight (fun x => component G u x + f2Dot a x) : Int) :=
        ⟨(2 : Int) ^ (2 * k - 3) + (2 : Int) ^ (k - 3), hWeight⟩
      exact_mod_cast hDivInt

def cosetFunction
    (G : V n -> V m) (h : V n -> ZMod 2) (u : V m) : V n -> ZMod 2 :=
  fun x => h x + component G u x

theorem exists_simultaneous_normalization
    (k : Nat) (hk : 3 <= k) (G : V (2 * k) -> V k)
    (h : V (2 * k) -> ZMod 2)
    (hBent : forall u, u ≠ 0 -> forall a,
      |walsh (component G u) a| = (2 : Int) ^ k)
    (hOdd : forall u, Odd (weight (cosetFunction G h u))) :
    exists gamma : Int,
      (gamma = 1 ∨ gamma = -1) ∧
      forall u a, exists c : Int,
        gamma * sign
            (f2Dot u (outputMoment G h) + f2Dot a (inputMoment h)) *
            halfWalsh (cosetFunction G h u) a =
          1 + 4 * c := by
  have hOddH : Odd (weight h) := by
    convert hOdd 0 using 1
    congr 2
    funext x
    simp [cosetFunction]
  obtain ⟨gamma, d, hgamma, hd⟩ :=
    exists_sign_decomposition_of_odd (weight h) hOddH
  refine ⟨gamma, hgamma, ?_⟩
  intro u a
  let r : V (2 * k) -> ZMod 2 :=
    fun x => component G u x + f2Dot a x
  let p : Nat := weight (fun x => h x * r x)
  obtain ⟨t, ht⟩ := four_dvd_weight_component_add_linear k hk G hBent u a
  have hShift :
      weight (fun x => cosetFunction G h u x + f2Dot a x) =
        weight (fun x => h x + r x) := by
    congr 1
    funext x
    simp [cosetFunction, r, add_assoc]
  have hWeightAdd := weight_add_eq h r
  have hHalf :
      halfWalsh (cosetFunction G h u) a =
        (2 : Int) ^ (2 * k - 1) - (weight h : Int) -
          (weight r : Int) + 2 * (p : Int) := by
    simp only [halfWalsh]
    rw [hShift, hWeightAdd]
    simp only [p]
    ring
  have hHalfPower : (2 : Int) ^ (2 * k - 1) =
      4 * (2 : Int) ^ (2 * k - 3) := by
    rw [show 2 * k - 1 = 2 + (2 * k - 3) by omega, pow_add]
    norm_num
  have htInt : (weight r : Int) = 4 * (t : Int) := by exact_mod_cast ht
  have hpCast : (p : ZMod 2) =
      f2Dot u (outputMoment G h) + f2Dot a (inputMoment h) := by
    exact product_weight_cast G h u a
  rcases zmod2_eq_zero_or_one
      (f2Dot u (outputMoment G h) + f2Dot a (inputMoment h)) with hbeta | hbeta
  · have hpEven : Even p := by
      apply ZMod.natCast_eq_zero_iff_even.mp
      exact hpCast.trans hbeta
    rcases hpEven with ⟨e, he⟩
    rcases hgamma with hgamma | hgamma
    · subst gamma
      simp [hbeta]
      refine ⟨(2 : Int) ^ (2 * k - 3) + d - (t : Int) + (e : Int), ?_⟩
      rw [hHalf, hHalfPower, htInt]
      norm_cast at he
      omega
    · subst gamma
      simp [hbeta]
      refine ⟨-(2 : Int) ^ (2 * k - 3) - d + (t : Int) - (e : Int), ?_⟩
      rw [hHalf, hHalfPower, htInt]
      norm_cast at he
      omega
  · have hpOdd : Odd p := by
      apply Nat.not_even_iff_odd.mp
      intro hpEven
      have hpZero : (p : ZMod 2) = 0 :=
        ZMod.natCast_eq_zero_iff_even.mpr hpEven
      rw [hpCast, hbeta] at hpZero
      norm_num at hpZero
    rcases hpOdd with ⟨e, he⟩
    rcases hgamma with hgamma | hgamma
    · subst gamma
      simp [hbeta]
      refine ⟨-(2 : Int) ^ (2 * k - 3) - d + (t : Int) - (e : Int) - 1, ?_⟩
      rw [hHalf, hHalfPower, htInt]
      norm_cast at he
      omega
    · subst gamma
      simp [hbeta]
      refine ⟨(2 : Int) ^ (2 * k - 3) + d - (t : Int) + (e : Int), ?_⟩
      rw [hHalf, hHalfPower, htInt]
      norm_cast at he
      omega

def fibreCard (G : V n -> V m) (y : V m) : Nat :=
  ((Finset.univ : Finset (V n)).filter fun x => G x = y).card

theorem fibreCard_eq_vectorialBent_fibreCard
    (G : V n -> V m) (y : V m) :
    fibreCard G y = LeanCipher.VectorialBent.fibreCard G y := by
  rw [fibreCard, LeanCipher.VectorialBent.fibreCard,
    Fintype.card_subtype (fun x : V n => G x = y)]

def fibreNegativeCount
    (G : V n -> V m) (h : V n -> ZMod 2) (a : V n) (y : V m) : Nat :=
  (((Finset.univ : Finset (V n)).filter fun x => G x = y).filter
    fun x => h x + f2Dot a x ≠ 0).card

def fibreSum
    (G : V n -> V m) (h : V n -> ZMod 2) (a : V n) (y : V m) : Int :=
  ((Finset.univ : Finset (V n)).filter (fun x => G x = y)).sum
    (fun x => sign (h x + f2Dot a x))

theorem fibreSum_eq_card_sub_two_mul
    (G : V n -> V m) (h : V n -> ZMod 2) (a : V n) (y : V m) :
    fibreSum G h a y = (fibreCard G y : Int) -
      2 * (fibreNegativeCount G h a y : Int) := by
  let s := (Finset.univ : Finset (V n)).filter fun x => G x = y
  have hIndicator :
      (s.sum fun x => if h x + f2Dot a x ≠ 0 then (1 : Int) else 0) =
        (fibreNegativeCount G h a y : Int) := by
    simpa [s, fibreNegativeCount] using
      (Finset.sum_boole (R := Int)
        (fun x : V n => h x + f2Dot a x ≠ 0) s)
  simp_rw [fibreSum, sign_eq_one_sub_two_indicator]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum]
  have hIndicator' :
      (((Finset.univ : Finset (V n)).filter fun x => G x = y).sum
        fun x => if h x + f2Dot a x ≠ 0 then (1 : Int) else 0) =
          (fibreNegativeCount G h a y : Int) := by
    simpa [s] using hIndicator
  rw [hIndicator']
  simp [fibreCard]

theorem fibreSum_odd
    (G : V n -> V m) (h : V n -> ZMod 2) (a : V n) (y : V m)
    (hOdd : Odd (fibreCard G y)) : Odd (fibreSum G h a y) := by
  rcases hOdd with ⟨d, hd⟩
  rw [fibreSum_eq_card_sub_two_mul]
  refine ⟨(d : Int) - (fibreNegativeCount G h a y : Int), ?_⟩
  omega

theorem walsh_coset_eq_fibre_hadamard
    (G : V n -> V m) (h : V n -> ZMod 2) (u : V m) (a : V n) :
    walsh (cosetFunction G h u) a =
      hadamardTransform (fun u y : V m => character u y)
        (fibreSum G h a) u := by
  classical
  have hWalsh : walsh (cosetFunction G h u) a =
      ∑ x, character u (G x) * sign (h x + f2Dot a x) := by
    apply Finset.sum_congr rfl
    intro x _
    simp only [cosetFunction, component_apply]
    rw [show h x + f2Dot u (G x) + f2Dot a x =
        f2Dot u (G x) + (h x + f2Dot a x) by
          rw [add_comm (h x) (f2Dot u (G x)), add_assoc]]
    simp [character]
  rw [hWalsh]
  simp only [hadamardTransform, fibreSum, Finset.mul_sum]
  calc
    (∑ x, character u (G x) * sign (h x + f2Dot a x)) =
        ∑ y, ((Finset.univ : Finset (V n)).filter
          (fun x => G x = y)).sum
          (fun x => character u (G x) * sign (h x + f2Dot a x)) := by
            symm
            simpa using
              (Finset.sum_fiberwise_eq_sum_filter
                (Finset.univ : Finset (V n)) (Finset.univ : Finset (V m)) G
                (fun x => character u (G x) * sign (h x + f2Dot a x)))
    _ = ∑ y, ((Finset.univ : Finset (V n)).filter
          (fun x => G x = y)).sum
          (fun x => character u y * sign (h x + f2Dot a x)) := by
            apply Finset.sum_congr rfl
            intro y _
            apply Finset.sum_congr rfl
            intro x hx
            have hxy : G x = y := (Finset.mem_filter.mp hx).2
            rw [hxy]

theorem normalized_square_eq_walsh_square
    (f : V n -> ZMod 2) (a : V n) (beta : ZMod 2)
    (gamma c : Int) (hn : 1 <= n)
    (hgamma : gamma = 1 ∨ gamma = -1)
    (hc : gamma * sign beta * halfWalsh f a = 1 + 4 * c) :
    4 * (1 + 4 * c) ^ 2 = walsh f a ^ 2 := by
  rw [← hc]
  have hgammaSq := gamma_sq hgamma
  have hsignSq := sign_sq beta
  have htwo := two_mul_halfWalsh f a hn
  calc
    4 * (gamma * sign beta * halfWalsh f a) ^ 2 =
        gamma ^ 2 * sign beta ^ 2 * (2 * halfWalsh f a) ^ 2 := by ring
    _ = (2 * halfWalsh f a) ^ 2 := by rw [hgammaSq, hsignSq]; ring
    _ = walsh f a ^ 2 := by rw [htwo]

theorem normalized_walsh_abs
    (f : V n -> ZMod 2) (a : V n) (beta : ZMod 2)
    (gamma c : Int) (hn : 1 <= n)
    (hgamma : gamma = 1 ∨ gamma = -1)
    (hc : gamma * sign beta * halfWalsh f a = 1 + 4 * c) :
    |2 * (1 + 4 * c)| = |walsh f a| := by
  rw [← hc, ← two_mul_halfWalsh f a hn]
  rcases hgamma with hgamma | hgamma <;> subst gamma <;>
    rcases sign_eq_one_or_neg_one beta with hsign | hsign <;>
      rw [hsign] <;> simp

theorem critical_coset_contradiction
    (k : Nat) (hk : 3 <= k) (G : V (2 * k) -> V k)
    (h : V (2 * k) -> ZMod 2)
    (hBent : forall u, u ≠ 0 -> forall a,
      |walsh (component G u) a| = (2 : Int) ^ k)
    (hOdd : forall u, Odd (weight (cosetFunction G h u)))
    (hCeiling : forall u a,
      |walsh (cosetFunction G h u) a| <= (2 : Int) ^ k + 2) :
    False := by
  obtain ⟨gamma, hgamma, hNormalization⟩ :=
    exists_simultaneous_normalization k hk G h hBent hOdd
  choose c hc using hNormalization
  let q : Nat := 2 ^ k
  let r : Nat := 2 ^ (k - 3)
  have hq : q = 8 * r := by
    dsimp [q, r]
    rw [show k = 3 + (k - 3) by omega, pow_add]
    norm_num
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hn : 1 <= 2 * k := by omega
  have hqCast : (q : Int) = (2 : Int) ^ k := by
    simp [q]
  have hNq : (2 : Int) ^ (2 * k) = (q : Int) ^ 2 := by
    rw [show 2 * k = k + k by omega, pow_add, hqCast]
    ring
  have hcardU : Fintype.card (V k) = q := by
    rw [f2Vec_card]
  have hcardA : Fintype.card (V (2 * k)) = q ^ 2 := by
    rw [f2Vec_card]
    dsimp [q]
    rw [show 2 * k = k + k by omega, pow_add]
    ring
  have hcardY : Fintype.card (V k) = q := hcardU
  have hBound : forall u a, |c u a| <= (r : Int) := by
    intro u a
    have hAbs := normalized_walsh_abs
      (cosetFunction G h u) a
      (f2Dot u (outputMoment G h) + f2Dot a (inputMoment h))
      gamma (c u a) hn hgamma (hc u a)
    have hCeil := hCeiling u a
    rw [← hAbs, ← hqCast] at hCeil
    rw [hq] at hCeil
    rw [abs_le] at hCeil ⊢
    constructor <;> omega
  have hRow : forall u,
      2 * (Finset.univ.sum fun a : V (2 * k) => 1 + 4 * c u a) =
          (q : Int) ^ 2 ∨
      2 * (Finset.univ.sum fun a : V (2 * k) => 1 + 4 * c u a) =
          -((q : Int) ^ 2) := by
    intro u
    have hSum :
        (Finset.univ.sum fun a : V (2 * k) => 1 + 4 * c u a) =
          Finset.univ.sum fun a : V (2 * k) =>
            gamma * sign
              (f2Dot u (outputMoment G h) + f2Dot a (inputMoment h)) *
              halfWalsh (cosetFunction G h u) a := by
      apply Finset.sum_congr rfl
      intro a _
      exact (hc u a).symm
    have hExact :
        2 * (Finset.univ.sum fun a : V (2 * k) => 1 + 4 * c u a) =
          gamma * sign (f2Dot u (outputMoment G h)) *
            ((2 : Int) ^ (2 * k) *
              sign (cosetFunction G h u (inputMoment h))) := by
      rw [hSum, Finset.mul_sum]
      calc
        (Finset.univ.sum fun a : V (2 * k) =>
            2 * (gamma * sign
              (f2Dot u (outputMoment G h) + f2Dot a (inputMoment h)) *
              halfWalsh (cosetFunction G h u) a)) =
            Finset.univ.sum fun a : V (2 * k) =>
              gamma * sign (f2Dot u (outputMoment G h)) *
                (walsh (cosetFunction G h u) a *
                  character a (inputMoment h)) := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [sign_add]
                    simp only [character]
                    rw [← two_mul_halfWalsh (cosetFunction G h u) a hn]
                    ring
        _ = gamma * sign (f2Dot u (outputMoment G h)) *
            (Finset.univ.sum fun a : V (2 * k) =>
              walsh (cosetFunction G h u) a * character a (inputMoment h)) := by
                rw [Finset.mul_sum]
        _ = gamma * sign (f2Dot u (outputMoment G h)) *
            ((2 : Int) ^ (2 * k) *
              sign (cosetFunction G h u (inputMoment h))) := by
                rw [walsh_inversion]
    rw [hNq] at hExact
    rcases hgamma with hgamma | hgamma <;> subst gamma <;>
      rcases sign_eq_one_or_neg_one (f2Dot u (outputMoment G h)) with hu | hu <;>
      rcases sign_eq_one_or_neg_one (cosetFunction G h u (inputMoment h)) with hf | hf <;>
      simp [hu, hf] at hExact ⊢ <;> tauto
  have hRowParseval : forall u,
      4 * (Finset.univ.sum fun a : V (2 * k) => (1 + 4 * c u a) ^ 2) =
        (q : Int) ^ 4 := by
    intro u
    calc
      4 * (Finset.univ.sum fun a : V (2 * k) => (1 + 4 * c u a) ^ 2) =
          Finset.univ.sum fun a : V (2 * k) =>
            4 * (1 + 4 * c u a) ^ 2 := by rw [Finset.mul_sum]
      _ = Finset.univ.sum fun a : V (2 * k) =>
          walsh (cosetFunction G h u) a ^ 2 := by
            apply Finset.sum_congr rfl
            intro a _
            exact normalized_square_eq_walsh_square
              (cosetFunction G h u) a
              (f2Dot u (outputMoment G h) + f2Dot a (inputMoment h))
              gamma (c u a) hn hgamma (hc u a)
      _ = ((2 : Int) ^ (2 * k)) ^ 2 := walsh_parseval _
      _ = (q : Int) ^ 4 := by rw [hNq]; ring
  have hVectorialBent : LeanCipher.VectorialBent.IsVectorialBent G := by
    intro u hu a
    exact hBent u hu a
  have hOddFibre : forall y, Odd (fibreCard G y) := by
    intro y
    rw [fibreCard_eq_vectorialBent_fibreCard]
    exact LeanCipher.VectorialBent.maximal_vectorial_bent_fibre_odd
      (by omega) hVectorialBent y
  let T : V (2 * k) -> V k -> Int := fun a y => fibreSum G h a y
  have hOddFibres : forall a y, Odd (T a y) := by
    intro a y
    exact fibreSum_odd G h a y (hOddFibre y)
  have hColumnParseval : forall a,
      4 * (Finset.univ.sum fun u : V k => (1 + 4 * c u a) ^ 2) =
        (q : Int) * (Finset.univ.sum fun y : V k => T a y ^ 2) := by
    intro a
    calc
      4 * (Finset.univ.sum fun u : V k => (1 + 4 * c u a) ^ 2) =
          Finset.univ.sum fun u : V k => 4 * (1 + 4 * c u a) ^ 2 := by
            rw [Finset.mul_sum]
      _ = Finset.univ.sum fun u : V k =>
          walsh (cosetFunction G h u) a ^ 2 := by
            apply Finset.sum_congr rfl
            intro u _
            exact normalized_square_eq_walsh_square
              (cosetFunction G h u) a
              (f2Dot u (outputMoment G h) + f2Dot a (inputMoment h))
              gamma (c u a) hn hgamma (hc u a)
      _ = Finset.univ.sum fun u : V k =>
          hadamardTransform (fun u y : V k => character u y) (T a) u ^ 2 := by
            apply Finset.sum_congr rfl
            intro u _
            rw [walsh_coset_eq_fibre_hadamard]
      _ = (2 : Int) ^ k * (Finset.univ.sum fun y : V k => T a y ^ 2) := by
            exact hadamard_parseval _ _ _ character_columns_orthogonal
      _ = (q : Int) * (Finset.univ.sum fun y : V k => T a y ^ 2) := by
            rw [hqCast]
  exact VectorialNonlinearity.criticalCosetContradiction
    (U := V k) (A := V (2 * k)) (Y := V k)
    q r hq hr hcardU hcardA hcardY c T hBound hRow hRowParseval
      hOddFibres hColumnParseval

end LeanCipher.VectorialCritical

import LeanCipher.F2
import Mathlib

open scoped BigOperators

namespace LeanCipher.BooleanWalsh

abbrev V (n : Nat) := LeanCipher.F2Vec n

def f2Dot (a x : V n) : ZMod 2 :=
  ∑ i, a i * x i

def sign (b : ZMod 2) : Int :=
  if b = 0 then 1 else -1

def character (a x : V n) : Int :=
  sign (f2Dot a x)

def component (F : V n -> V m) (b : V m) : V n -> ZMod 2 :=
  fun x => f2Dot b (F x)

@[simp]
theorem component_apply (F : V n -> V m) (b : V m) (x : V n) :
    component F b x = f2Dot b (F x) := rfl

@[simp]
theorem component_zero (F : V n -> V m) : component F 0 = 0 := by
  funext x
  simp [component, f2Dot]

@[simp]
theorem component_add (F : V n -> V m) (b c : V m) :
    component F (b + c) = component F b + component F c := by
  funext x
  simp [component, f2Dot, add_mul, Finset.sum_add_distrib]

def weight (f : V n -> ZMod 2) : Nat :=
  ((Finset.univ : Finset (V n)).filter fun x => f x ≠ 0).card

def walsh (f : V n -> ZMod 2) (a : V n) : Int :=
  ∑ x, sign (f x + f2Dot a x)

theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmod2_eq_one_of_ne_zero {b : ZMod 2} (hb : b ≠ 0) : b = 1 := by
  rcases zmod2_eq_zero_or_one b with h | h
  · exact (hb h).elim
  · exact h

alias f2_eq_zero_or_one := zmod2_eq_zero_or_one

@[simp]
theorem sign_zero : sign 0 = 1 := by
  simp [sign]

@[simp]
theorem sign_one : sign 1 = -1 := by
  simp [sign]

theorem sign_eq_one_iff (b : ZMod 2) : sign b = 1 ↔ b = 0 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp

theorem sign_eq_neg_one_iff (b : ZMod 2) : sign b = -1 ↔ b = 1 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp

@[simp]
theorem sign_add (b c : ZMod 2) : sign (b + c) = sign b * sign c := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;>
      simp [sign, CharTwo.add_self_eq_zero]

@[simp]
theorem sign_sq (b : ZMod 2) : sign b ^ 2 = 1 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> norm_num

@[simp]
theorem f2Dot_zero_left (x : V n) : f2Dot 0 x = 0 := by
  simp [f2Dot]

@[simp]
theorem f2Dot_zero_right (a : V n) : f2Dot a 0 = 0 := by
  simp [f2Dot]

@[simp]
theorem f2Dot_add_left (a b x : V n) :
    f2Dot (a + b) x = f2Dot a x + f2Dot b x := by
  simp [f2Dot, add_mul, Finset.sum_add_distrib]

@[simp]
theorem f2Dot_add_right (a x y : V n) :
    f2Dot a (x + y) = f2Dot a x + f2Dot a y := by
  simp [f2Dot, mul_add, Finset.sum_add_distrib]

theorem f2Dot_comm (a x : V n) : f2Dot a x = f2Dot x a := by
  simp only [f2Dot, mul_comm]

@[simp]
theorem character_zero_left (x : V n) : character 0 x = 1 := by
  simp [character]

@[simp]
theorem character_zero_right (a : V n) : character a 0 = 1 := by
  simp [character]

@[simp]
theorem character_add_left (a b x : V n) :
    character (a + b) x = character a x * character b x := by
  simp [character]

@[simp]
theorem character_add_right (a x y : V n) :
    character a (x + y) = character a x * character a y := by
  simp [character]

theorem character_comm (a x : V n) : character a x = character x a := by
  simp only [character, f2Dot_comm]

@[simp]
theorem character_sq (a x : V n) : character a x ^ 2 = 1 := by
  simp [character]

theorem f2Vec_card (n : Nat) : Fintype.card (V n) = 2 ^ n := by
  simp [V, LeanCipher.F2Vec]

theorem f2Vec_finrank (n : Nat) : Module.finrank (ZMod 2) (V n) = n := by
  simp [V, LeanCipher.F2Vec]

def basisVector (i : Fin n) : V n :=
  fun j => if j = i then 1 else 0

@[simp]
theorem basisVector_apply_self (i : Fin n) : basisVector i i = 1 := by
  simp [basisVector]

@[simp]
theorem f2Dot_basis_right (a : V n) (i : Fin n) :
    f2Dot a (basisVector i) = a i := by
  classical
  simp [f2Dot, basisVector]

@[simp]
theorem f2Dot_basis_left (i : Fin n) (x : V n) :
    f2Dot (basisVector i) x = x i := by
  rw [f2Dot_comm, f2Dot_basis_right]

theorem exists_ne_zero_coordinate {a : V n} (ha : a ≠ 0) :
    exists i, a i ≠ 0 := by
  by_contra h
  apply ha
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

theorem f2Dot_left_surjective {a : V n} (ha : a ≠ 0) :
    Function.Surjective (f2Dot a) := by
  intro z
  rcases zmod2_eq_zero_or_one z with rfl | rfl
  · exact ⟨0, f2Dot_zero_right a⟩
  · obtain ⟨i, hi⟩ := exists_ne_zero_coordinate ha
    refine ⟨basisVector i, ?_⟩
    rw [f2Dot_basis_right]
    exact zmod2_eq_one_of_ne_zero hi

theorem f2Dot_right_surjective {x : V n} (hx : x ≠ 0) :
    Function.Surjective (fun a => f2Dot a x) := by
  intro z
  obtain ⟨a, ha⟩ := f2Dot_left_surjective hx z
  exact ⟨a, f2Dot_comm a x |>.trans ha⟩

def characterAddChar (a : V n) : AddChar (V n) Int where
  toFun := character a
  map_zero_eq_one' := character_zero_right a
  map_add_eq_mul' := character_add_right a

@[simp]
theorem characterAddChar_apply (a x : V n) :
    characterAddChar a x = character a x := rfl

theorem characterAddChar_eq_zero_iff (a : V n) :
    characterAddChar a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext i
    have hi := DFunLike.congr_fun h (basisVector i)
    simp only [characterAddChar_apply, AddChar.zero_apply, character, f2Dot_basis_right] at hi
    exact sign_eq_one_iff (a i) |>.mp hi
  · rintro rfl
    ext x
    simp

theorem character_sum (a : V n) :
    (∑ x, character a x) = if a = 0 then (2 : Int) ^ n else 0 := by
  rw [show (∑ x, character a x) = ∑ x, characterAddChar a x by rfl]
  rw [AddChar.sum_eq_ite]
  simp only [characterAddChar_eq_zero_iff]
  split_ifs <;> simp_all

theorem add_eq_zero_iff_eq {a b : V n} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc
      a = a + b + b := (LeanCipher.f2vec_cancel_right a b).symm
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact LeanCipher.f2vec_add_self a

theorem character_orthogonality (a b : V n) :
    (∑ x, character a x * character b x) =
      if a = b then (2 : Int) ^ n else 0 := by
  calc
    (∑ x, character a x * character b x) =
        ∑ x, character (a + b) x := by
          apply Finset.sum_congr rfl
          intro x _
          exact (character_add_left a b x).symm
    _ = if a + b = 0 then (2 : Int) ^ n else 0 := character_sum (a + b)
    _ = if a = b then (2 : Int) ^ n else 0 := by
      split_ifs <;> simp_all [add_eq_zero_iff_eq]

theorem sign_eq_one_sub_two_indicator (b : ZMod 2) :
    sign b = 1 - 2 * if b ≠ 0 then 1 else 0 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp

theorem sum_sign_eq_card_sub_two_mul_weight (f : V n -> ZMod 2) :
    (∑ x, sign (f x)) = (2 : Int) ^ n - 2 * (weight f : Int) := by
  have hIndicator :
      (∑ x : V n, if f x ≠ 0 then (1 : Int) else 0) = (weight f : Int) := by
    simpa [weight] using
      (Finset.sum_boole (R := Int) (fun x : V n => f x ≠ 0)
        (Finset.univ : Finset (V n)))
  simp_rw [sign_eq_one_sub_two_indicator]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, hIndicator]
  rw [f2Vec_card]
  push_cast
  simp

theorem weight_le_card (f : V n -> ZMod 2) : weight f ≤ 2 ^ n := by
  rw [← f2Vec_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

@[simp]
theorem weight_zero : weight (fun _ : V n => (0 : ZMod 2)) = 0 := by
  simp [weight]

@[simp]
theorem weight_one : weight (fun _ : V n => (1 : ZMod 2)) = 2 ^ n := by
  simp [weight]

theorem sum_eq_weight_cast_zmod2 (f : V n -> ZMod 2) :
    (∑ x, f x) = (weight f : ZMod 2) := by
  calc
    (∑ x, f x) = ∑ x, if f x ≠ 0 then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases zmod2_eq_zero_or_one (f x) with h | h <;> simp [h]
    _ = (weight f : ZMod 2) := by
      simpa [weight] using
        (Finset.sum_boole (R := ZMod 2) (fun x : V n => f x ≠ 0)
          (Finset.univ : Finset (V n)))

theorem weight_cast_zmod2 (f : V n -> ZMod 2) :
    (weight f : ZMod 2) = ∑ x, f x :=
  (sum_eq_weight_cast_zmod2 f).symm

theorem weight_even_iff_sum_eq_zero (f : V n -> ZMod 2) :
    Even (weight f) ↔ (∑ x, f x) = 0 := by
  rw [sum_eq_weight_cast_zmod2]
  exact ZMod.natCast_eq_zero_iff_even.symm

theorem weight_add_cast_zmod2 (f g : V n -> ZMod 2) :
    (weight (fun x => f x + g x) : ZMod 2) =
      (weight f : ZMod 2) + (weight g : ZMod 2) := by
  rw [weight_cast_zmod2, weight_cast_zmod2, weight_cast_zmod2]
  exact Finset.sum_add_distrib

theorem weight_add_even_iff (f g : V n -> ZMod 2) :
    Even (weight fun x => f x + g x) ↔
      (Even (weight f) ↔ Even (weight g)) := by
  rw [← ZMod.natCast_eq_zero_iff_even, weight_add_cast_zmod2,
    ← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even]
  rcases zmod2_eq_zero_or_one (weight f : ZMod 2) with hf | hf <;>
    rcases zmod2_eq_zero_or_one (weight g : ZMod 2) with hg | hg <;>
      simp [hf, hg, CharTwo.add_self_eq_zero]

theorem walsh_eq_card_sub_two_mul_weight (f : V n -> ZMod 2) (a : V n) :
    walsh f a = (2 : Int) ^ n -
      2 * (weight fun x => f x + f2Dot a x : Int) := by
  exact sum_sign_eq_card_sub_two_mul_weight (fun x => f x + f2Dot a x)

theorem two_mul_linear_weight (a : V n) (ha : a ≠ 0) :
    2 * weight (fun x => f2Dot a x) = 2 ^ n := by
  have hCharacter : (∑ x, sign (f2Dot a x)) = 0 := by
    simpa only [character] using (character_sum a |>.trans (if_neg ha))
  have hWeight := sum_sign_eq_card_sub_two_mul_weight (fun x => f2Dot a x)
  rw [hCharacter] at hWeight
  exact_mod_cast (by omega : (2 : Int) * weight (fun x => f2Dot a x) = (2 : Int) ^ n)

theorem linear_weight (a : V n) (ha : a ≠ 0) :
    weight (fun x => f2Dot a x) = 2 ^ (n - 1) := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    apply ha
    funext i
    exact Fin.elim0 i
  have h := two_mul_linear_weight a ha
  have hPow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ (1 + (n - 1)) := by congr 1; omega
      _ = 2 * 2 ^ (n - 1) := by rw [pow_add]; norm_num
  omega

theorem linear_weight_zero :
    weight (fun x : V n => f2Dot 0 x) = 0 := by
  simp [weight]

theorem linear_weight_even (a : V n) (hn : 2 ≤ n) :
    Even (weight fun x => f2Dot a x) := by
  by_cases ha : a = 0
  · subst a
    rw [show weight (fun x : V n => f2Dot 0 x) = 0 by simp [weight]]
    exact ⟨0, by simp⟩
  · rw [linear_weight a ha]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    exact even_iff_two_dvd.mpr ⟨2 ^ (n - 2), by omega⟩

theorem four_dvd_walsh_of_weight_even
    (f : V n -> ZMod 2) (a : V n) (hn : 2 ≤ n)
    (hf : Even (weight f)) : (4 : Int) ∣ walsh f a := by
  have hLinear := linear_weight_even a hn
  have hShift : Even (weight fun x => f x + f2Dot a x) :=
    (weight_add_even_iff f (fun x => f2Dot a x)).mpr (iff_of_true hf hLinear)
  obtain ⟨r, hr⟩ := hShift
  refine ⟨(2 : Int) ^ (n - 2) - r, ?_⟩
  rw [walsh_eq_card_sub_two_mul_weight, hr]
  rw [show n = 2 + (n - 2) by omega, pow_add]
  norm_num
  ring

theorem walsh_eq_sum_sign_mul_character (f : V n -> ZMod 2) (a : V n) :
    walsh f a = ∑ x, sign (f x) * character a x := by
  apply Finset.sum_congr rfl
  intro x _
  simp [character]

section Hadamard

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

def hadamardTransform (H : A -> B -> Int) (v : B -> Int) : A -> Int :=
  fun a => ∑ x, H a x * v x

def HasOrthogonalColumns (H : A -> B -> Int) (q : Int) : Prop :=
  forall x y, (∑ a, H a x * H a y) = if x = y then q else 0

theorem hadamard_inversion
    (H : A -> B -> Int) (v : B -> Int) (q : Int)
    (hH : HasOrthogonalColumns H q) (x : B) :
    (∑ a, hadamardTransform H v a * H a x) = q * v x := by
  classical
  calc
    (∑ a, hadamardTransform H v a * H a x) =
        ∑ a, ∑ y, (H a y * v y) * H a x := by
          simp only [hadamardTransform, Finset.sum_mul]
    _ = ∑ y, ∑ a, (H a y * v y) * H a x := Finset.sum_comm
    _ = ∑ y, v y * (∑ a, H a y * H a x) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ∑ y, v y * (if y = x then q else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hH y x]
    _ = q * v x := by simp [mul_comm]

theorem hadamard_parseval
    (H : A -> B -> Int) (v : B -> Int) (q : Int)
    (hH : HasOrthogonalColumns H q) :
    (∑ a, hadamardTransform H v a ^ 2) =
      q * ∑ x, v x ^ 2 := by
  classical
  calc
    (∑ a, hadamardTransform H v a ^ 2) =
        ∑ a, hadamardTransform H v a * (∑ x, H a x * v x) := by
          apply Finset.sum_congr rfl
          intro a _
          simp [hadamardTransform, pow_two]
    _ = ∑ a, ∑ x, hadamardTransform H v a * (H a x * v x) := by
          simp only [Finset.mul_sum]
    _ = ∑ x, ∑ a, hadamardTransform H v a * (H a x * v x) := Finset.sum_comm
    _ = ∑ x, v x * (∑ a, hadamardTransform H v a * H a x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ∑ x, v x * (q * v x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hadamard_inversion H v q hH x]
    _ = q * ∑ x, v x ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

end Hadamard

theorem character_columns_orthogonal :
    HasOrthogonalColumns (fun a x : V n => character a x) ((2 : Int) ^ n) := by
  intro x y
  calc
    (∑ a, character a x * character a y) =
        ∑ a, character x a * character y a := by
          apply Finset.sum_congr rfl
          intro a _
          rw [character_comm a x, character_comm a y]
    _ = if x = y then (2 : Int) ^ n else 0 := character_orthogonality x y

theorem walsh_eq_hadamardTransform (f : V n -> ZMod 2) :
    walsh f = hadamardTransform
      (fun a x : V n => character a x) (fun x => sign (f x)) := by
  funext a
  rw [walsh_eq_sum_sign_mul_character]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem walsh_inversion (f : V n -> ZMod 2) (x : V n) :
    (∑ a, walsh f a * character a x) =
      (2 : Int) ^ n * sign (f x) := by
  rw [walsh_eq_hadamardTransform]
  exact hadamard_inversion _ _ _ character_columns_orthogonal x

theorem walsh_parseval (f : V n -> ZMod 2) :
    (∑ a, walsh f a ^ 2) = ((2 : Int) ^ n) ^ 2 := by
  rw [walsh_eq_hadamardTransform]
  rw [hadamard_parseval _ _ _ character_columns_orthogonal]
  calc
    (2 : Int) ^ n * ∑ x : V n, sign (f x) ^ 2 =
        (2 : Int) ^ n * Fintype.card (V n) := by simp
    _ = ((2 : Int) ^ n) ^ 2 := by
      rw [f2Vec_card]
      push_cast
      ring

end LeanCipher.BooleanWalsh

import LeanCipher.BalancedEightCore
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEight

open LeanCipher.BooleanWalsh

/-!
# Seven-variable slices of an eight-variable Boolean function

The last coordinate is separated explicitly.  For each odd frequency direction
`join ell 1`, the involution `shear ell` is the primal change of variables dual
to the frequency map `(a,b) |-> (a + b ell,b)`.  Consequently the Walsh
coefficients on the paired frequencies are the sum and difference of the two
seven-variable slice spectra.
-/

def join (x : V 7) (b : ZMod 2) : V 8 :=
  Fin.snoc x b

def head (x : V 8) : V 7 :=
  Fin.init x

def last (x : V 8) : ZMod 2 :=
  x (Fin.last 7)

@[simp] theorem head_join (x : V 7) (b : ZMod 2) :
    head (join x b) = x := by
  simp [head, join]

@[simp] theorem last_join (x : V 7) (b : ZMod 2) :
    last (join x b) = b := by
  change (@Fin.snoc 7 (fun _ : Fin 8 => ZMod 2) x b (Fin.last 7)) = b
  simp [Fin.snoc]

@[simp] theorem join_head_last (x : V 8) :
    join (head x) (last x) = x := by
  simpa [join, head, last] using Fin.snoc_init_self x

def splitEquiv : V 8 ≃ V 7 × ZMod 2 where
  toFun x := (head x, last x)
  invFun x := join x.1 x.2
  left_inv := join_head_last
  right_inv x := by simp

@[simp] theorem splitEquiv_apply (x : V 8) :
    splitEquiv x = (head x, last x) := rfl

@[simp] theorem splitEquiv_symm_apply (x : V 7 × ZMod 2) :
    splitEquiv.symm x = join x.1 x.2 := rfl

theorem f2Dot_join (a x : V 7) (b y : ZMod 2) :
    f2Dot (join a b) (join x y) = f2Dot a x + b * y := by
  unfold f2Dot
  rw [Fin.sum_univ_castSucc]
  simp only [join, Fin.snoc_castSucc, Fin.snoc_last]

theorem character_join (a x : V 7) (b y : ZMod 2) :
    character (join a b) (join x y) =
      character a x * sign (b * y) := by
  simp [character, f2Dot_join]

def lowerSlice (f : V 8 -> ZMod 2) : V 7 -> ZMod 2 :=
  fun x => f (join x 0)

def upperSlice (f : V 8 -> ZMod 2) : V 7 -> ZMod 2 :=
  fun x => f (join x 1)

theorem walsh_join_eq_slice_sum
    (f : V 8 -> ZMod 2) (a : V 7) :
    walsh f (join a 0) = walsh (lowerSlice f) a + walsh (upperSlice f) a := by
  classical
  rw [walsh_eq_sum_sign_mul_character]
  have hsplit := splitEquiv.sum_comp
    (fun y : V 7 × ZMod 2 =>
      sign (f (join y.1 y.2)) * character (join a 0) (join y.1 y.2))
  rw [show
      (∑ x : V 8, sign (f x) * character (join a 0) x) =
        ∑ y : V 7 × ZMod 2,
          sign (f (join y.1 y.2)) * character (join a 0) (join y.1 y.2) by
    simpa using hsplit]
  rw [Fintype.sum_prod_type]
  simp only [character_join, zero_mul, sign_zero, mul_one]
  rw [walsh_eq_sum_sign_mul_character, walsh_eq_sum_sign_mul_character]
  simp only [lowerSlice, upperSlice]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by native_decide]
  simp

theorem walsh_join_eq_slice_difference
    (f : V 8 -> ZMod 2) (a : V 7) :
    walsh f (join a 1) = walsh (lowerSlice f) a - walsh (upperSlice f) a := by
  classical
  rw [walsh_eq_sum_sign_mul_character]
  have hsplit := splitEquiv.sum_comp
    (fun y : V 7 × ZMod 2 =>
      sign (f (join y.1 y.2)) * character (join a 1) (join y.1 y.2))
  rw [show
      (∑ x : V 8, sign (f x) * character (join a 1) x) =
        ∑ y : V 7 × ZMod 2,
          sign (f (join y.1 y.2)) * character (join a 1) (join y.1 y.2) by
    simpa using hsplit]
  rw [Fintype.sum_prod_type]
  simp only [character_join, one_mul]
  rw [walsh_eq_sum_sign_mul_character, walsh_eq_sum_sign_mul_character]
  simp only [lowerSlice, upperSlice]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by native_decide]
  simp [sub_eq_add_neg]

def shear (ell : V 7) (x : V 8) : V 8 :=
  join (head x) (last x + f2Dot ell (head x))

@[simp] theorem head_shear (ell : V 7) (x : V 8) :
    head (shear ell x) = head x := by
  simp [shear]

@[simp] theorem last_shear (ell : V 7) (x : V 8) :
    last (shear ell x) = last x + f2Dot ell (head x) := by
  simp [shear]

theorem shear_involutive (ell : V 7) : Function.Involutive (shear ell) := by
  intro x
  simp only [shear, head_join, last_join]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, join_head_last]

def shearEquiv (ell : V 7) : V 8 ≃ V 8 :=
  { toFun := shear ell
    invFun := shear ell
    left_inv := shear_involutive ell
    right_inv := shear_involutive ell }

@[simp] theorem shearEquiv_apply (ell : V 7) (x : V 8) :
    shearEquiv ell x = shear ell x := rfl

def frequencyShear (ell : V 7) (a : V 8) : V 8 :=
  join (head a + last a • ell) (last a)

theorem f2Dot_frequencyShear (ell : V 7) (a x : V 8) :
    f2Dot (frequencyShear ell a) x = f2Dot a (shear ell x) := by
  rw [← join_head_last x, ← join_head_last a]
  simp only [frequencyShear, head_join, last_join, shear]
  rw [f2Dot_join, f2Dot_join]
  simp only [f2Dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hmul :
      (∑ i, last a * ell i * head x i) =
        last a * ∑ i, ell i * head x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmul]
  ring

theorem walsh_comp_shear (f : V 8 -> ZMod 2) (ell : V 7) (a : V 8) :
    walsh (fun x => f (shear ell x)) a = walsh f (frequencyShear ell a) := by
  classical
  unfold walsh
  have hsum := (shearEquiv ell).sum_comp
    (fun x : V 8 => sign (f x + f2Dot (frequencyShear ell a) x))
  calc
    (∑ x : V 8, sign (f (shear ell x) + f2Dot a x)) =
        ∑ x : V 8,
          sign (f (shear ell x) +
            f2Dot (frequencyShear ell a) (shear ell x)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [f2Dot_frequencyShear]
          rw [shear_involutive ell x]
    _ = ∑ x : V 8, sign (f x + f2Dot (frequencyShear ell a) x) := by
          simpa using hsum

def directionLowerSlice (f : V 8 -> ZMod 2) (ell : V 7) :
    V 7 -> ZMod 2 :=
  lowerSlice (fun x => f (shear ell x))

def directionUpperSlice (f : V 8 -> ZMod 2) (ell : V 7) :
    V 7 -> ZMod 2 :=
  upperSlice (fun x => f (shear ell x))

theorem frequencyShear_join_zero (ell a : V 7) :
    frequencyShear ell (join a 0) = join a 0 := by
  simp [frequencyShear]

theorem frequencyShear_join_one (ell a : V 7) :
    frequencyShear ell (join a 1) = join (a + ell) 1 := by
  simp [frequencyShear]

theorem direction_slice_sum (f : V 8 -> ZMod 2) (ell a : V 7) :
    walsh f (join a 0) =
      walsh (directionLowerSlice f ell) a +
        walsh (directionUpperSlice f ell) a := by
  rw [← frequencyShear_join_zero ell a, ← walsh_comp_shear]
  exact walsh_join_eq_slice_sum (fun x => f (shear ell x)) a

theorem direction_slice_difference (f : V 8 -> ZMod 2) (ell a : V 7) :
    walsh f (join (a + ell) 1) =
      walsh (directionLowerSlice f ell) a -
        walsh (directionUpperSlice f ell) a := by
  rw [← frequencyShear_join_one ell a, ← walsh_comp_shear]
  exact walsh_join_eq_slice_difference (fun x => f (shear ell x)) a

end LeanCipher.BalancedEight

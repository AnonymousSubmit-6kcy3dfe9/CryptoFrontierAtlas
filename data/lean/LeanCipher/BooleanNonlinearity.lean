import LeanCipher.BooleanWalsh
import Mathlib

open scoped BigOperators

namespace LeanCipher.BooleanNonlinearity

open LeanCipher.BooleanWalsh

/-!
# Boolean nonlinearity and affine distance

This module connects the Walsh-spectrum definition of Boolean nonlinearity
with its coding-theoretic definition as minimum Hamming distance to an affine
Boolean function.  The definition

`(2^n - max_a |W_f(a)|) / 2`

is valid also for `n = 0`; in that case every Boolean function is constant and
has nonlinearity zero.
-/

def hammingDistance (f g : V n -> ZMod 2) : Nat :=
  weight fun x => f x + g x

theorem hammingDistance_eq_card_filter_ne (f g : V n -> ZMod 2) :
    hammingDistance f g =
      ((Finset.univ : Finset (V n)).filter fun x => f x ≠ g x).card := by
  unfold hammingDistance weight
  congr 1
  ext x
  rcases zmod2_eq_zero_or_one (f x) with hf | hf <;>
    rcases zmod2_eq_zero_or_one (g x) with hg | hg <;>
      simp [hf, hg, CharTwo.add_self_eq_zero]

def affineFunction (a : V n) (c : ZMod 2) : V n -> ZMod 2 :=
  fun x => f2Dot a x + c

def maximumWalshMagnitude (f : V n -> ZMod 2) : Nat :=
  (Finset.univ : Finset (V n)).sup fun a => (walsh f a).natAbs

def nonlinearity (f : V n -> ZMod 2) : Nat :=
  (2 ^ n - maximumWalshMagnitude f) / 2

def affineDistanceValues (f : V n -> ZMod 2) : Finset Nat :=
  (Finset.univ : Finset (V n × ZMod 2)).image fun p =>
    hammingDistance f (affineFunction p.1 p.2)

theorem affineDistanceValues_nonempty (f : V n -> ZMod 2) :
    (affineDistanceValues f).Nonempty := by
  refine ⟨hammingDistance f (affineFunction 0 0), ?_⟩
  simp [affineDistanceValues]

def distanceToAffine (f : V n -> ZMod 2) : Nat :=
  (affineDistanceValues f).min' (affineDistanceValues_nonempty f)

theorem walsh_natAbs_le_card (f : V n -> ZMod 2) (a : V n) :
    (walsh f a).natAbs <= 2 ^ n := by
  have hweight := weight_le_card (fun x => f x + f2Dot a x)
  have hwalsh := walsh_eq_card_sub_two_mul_weight f a
  have hweightInt :
      (weight (fun x => f x + f2Dot a x) : Int) <= (2 : Int) ^ n := by
    exact_mod_cast hweight
  have hlower : -((2 : Int) ^ n) <= walsh f a := by
    rw [hwalsh]
    omega
  have hupper : walsh f a <= (2 : Int) ^ n := by
    rw [hwalsh]
    have : (0 : Int) <= weight (fun x => f x + f2Dot a x) := by positivity
    omega
  have habs : |walsh f a| <= (2 : Int) ^ n :=
    abs_le.mpr ⟨hlower, hupper⟩
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

theorem maximumWalshMagnitude_le_card (f : V n -> ZMod 2) :
    maximumWalshMagnitude f <= 2 ^ n := by
  apply Finset.sup_le
  intro a _
  exact walsh_natAbs_le_card f a

theorem walsh_natAbs_le_maximum (f : V n -> ZMod 2) (a : V n) :
    (walsh f a).natAbs <= maximumWalshMagnitude f := by
  exact Finset.le_sup (s := (Finset.univ : Finset (V n)))
    (f := fun b => (walsh f b).natAbs) (Finset.mem_univ a)

theorem exists_walsh_natAbs_eq_maximum (f : V n -> ZMod 2) :
    exists a : V n, (walsh f a).natAbs = maximumWalshMagnitude f := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (V n)) Finset.univ_nonempty
    (fun a => (walsh f a).natAbs)
  exact ⟨a, ha.symm⟩

theorem two_dvd_walsh (f : V n -> ZMod 2) (a : V n) (hn : 1 <= n) :
    (2 : Int) ∣ walsh f a := by
  rw [walsh_eq_card_sub_two_mul_weight]
  refine ⟨(2 : Int) ^ (n - 1) -
      (weight (fun x => f x + f2Dot a x) : Int), ?_⟩
  have hpow : (2 : Int) ^ n = 2 * (2 : Int) ^ (n - 1) := by
    calc
      (2 : Int) ^ n = 2 ^ (1 + (n - 1)) := by congr 1; omega
      _ = 2 * (2 : Int) ^ (n - 1) := by rw [pow_add]; norm_num
  rw [hpow]
  ring

theorem walsh_natAbs_even (f : V n -> ZMod 2) (a : V n) (hn : 1 <= n) :
    Even (walsh f a).natAbs := by
  obtain ⟨q, hq⟩ := two_dvd_walsh f a hn
  refine ⟨q.natAbs, ?_⟩
  rw [hq, Int.natAbs_mul]
  norm_num
  omega

theorem maximumWalshMagnitude_even (f : V n -> ZMod 2) (hn : 1 <= n) :
    Even (maximumWalshMagnitude f) := by
  obtain ⟨a, ha⟩ := exists_walsh_natAbs_eq_maximum f
  rw [← ha]
  exact walsh_natAbs_even f a hn

theorem nonlinearity_eq_paper_formula
    (f : V n -> ZMod 2) (hn : 1 <= n) :
    nonlinearity f = 2 ^ (n - 1) - maximumWalshMagnitude f / 2 := by
  obtain ⟨q, hq⟩ := maximumWalshMagnitude_even f hn
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ (1 + (n - 1)) := by congr 1; omega
      _ = 2 * 2 ^ (n - 1) := by rw [pow_add]; norm_num
  have hmax := maximumWalshMagnitude_le_card f
  unfold nonlinearity
  rw [hpow, hq]
  omega

theorem walsh_add_constant
    (f : V n -> ZMod 2) (c : ZMod 2) (a : V n) :
    walsh (fun x => f x + c) a = sign c * walsh f a := by
  unfold walsh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [show f x + c + f2Dot a x = c + (f x + f2Dot a x) by ac_rfl]
  exact sign_add c (f x + f2Dot a x)

theorem affine_distance_walsh_identity
    (f : V n -> ZMod 2) (a : V n) (c : ZMod 2) :
    2 * (hammingDistance f (affineFunction a c) : Int) =
      (2 : Int) ^ n - sign c * walsh f a := by
  have hwalsh := walsh_eq_card_sub_two_mul_weight
    (fun x => f x + c) a
  rw [walsh_add_constant] at hwalsh
  have hdistance :
      weight (fun x => (f x + c) + f2Dot a x) =
        hammingDistance f (affineFunction a c) := by
    congr 1
    funext x
    simp only [affineFunction]
    ac_rfl
  rw [hdistance] at hwalsh
  linarith

theorem exists_affine_at_nonlinearity (f : V n -> ZMod 2) :
    exists a : V n, exists c : ZMod 2,
      hammingDistance f (affineFunction a c) = nonlinearity f := by
  obtain ⟨a, ha⟩ := exists_walsh_natAbs_eq_maximum f
  let c : ZMod 2 := if 0 <= walsh f a then 0 else 1
  have hsign : sign c * walsh f a =
      (maximumWalshMagnitude f : Int) := by
    dsimp [c]
    split_ifs with hnonneg
    · simp only [sign_zero, one_mul]
      calc
        walsh f a = ((walsh f a).natAbs : Int) :=
          (Int.natAbs_of_nonneg hnonneg).symm
        _ = (maximumWalshMagnitude f : Int) := by exact_mod_cast ha
    · have hnonpos : walsh f a <= 0 := le_of_not_ge hnonneg
      simp only [BooleanWalsh.sign_one, neg_one_mul]
      calc
        -walsh f a = |walsh f a| := (abs_of_nonpos hnonpos).symm
        _ = ((walsh f a).natAbs : Int) := Int.abs_eq_natAbs _
        _ = (maximumWalshMagnitude f : Int) := by exact_mod_cast ha
  have hidentity := affine_distance_walsh_identity f a c
  rw [hsign] at hidentity
  have hmax := maximumWalshMagnitude_le_card f
  have hnat :
      2 * hammingDistance f (affineFunction a c) =
        2 ^ n - maximumWalshMagnitude f := by
    rw [← Nat.cast_inj (R := Int), Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub hmax, Nat.cast_pow, Nat.cast_ofNat]
    exact hidentity
  refine ⟨a, c, ?_⟩
  unfold nonlinearity
  omega

theorem nonlinearity_le_affine_distance
    (f : V n -> ZMod 2) (a : V n) (c : ZMod 2) :
    nonlinearity f <= hammingDistance f (affineFunction a c) := by
  have htarget := affine_distance_walsh_identity f a c
  have hsignLeAbs : sign c * walsh f a <= |walsh f a| := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simpa using le_abs_self (walsh f a)
    · simpa only [BooleanWalsh.sign_one, neg_one_mul] using
        neg_le_abs (walsh f a)
  have habsLeMax : |walsh f a| <= (maximumWalshMagnitude f : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast walsh_natAbs_le_maximum f a
  have hmax := maximumWalshMagnitude_le_card f
  have hdiffInt :
      ((2 ^ n - maximumWalshMagnitude f : Nat) : Int) <=
        2 * (hammingDistance f (affineFunction a c) : Int) := by
    rw [Nat.cast_sub hmax, Nat.cast_pow, Nat.cast_ofNat, htarget]
    exact sub_le_sub_left (hsignLeAbs.trans habsLeMax) _
  have hdiffNat :
      2 ^ n - maximumWalshMagnitude f <=
        2 * hammingDistance f (affineFunction a c) := by
    exact_mod_cast hdiffInt
  unfold nonlinearity
  exact Nat.div_le_of_le_mul hdiffNat

theorem distanceToAffine_eq_nonlinearity (f : V n -> ZMod 2) :
    distanceToAffine f = nonlinearity f := by
  apply Nat.le_antisymm
  · obtain ⟨a, c, hac⟩ := exists_affine_at_nonlinearity f
    rw [← hac]
    apply Finset.min'_le
    simp [affineDistanceValues]
  · apply Finset.le_min'
    intro d hd
    rw [affineDistanceValues, Finset.mem_image] at hd
    obtain ⟨p, _, rfl⟩ := hd
    exact nonlinearity_le_affine_distance f p.1 p.2

theorem nonlinearity_eq_minimum_affine_hamming_distance
    (f : V n -> ZMod 2) :
    nonlinearity f = distanceToAffine f :=
  (distanceToAffine_eq_nonlinearity f).symm

@[simp]
theorem nonlinearity_zero_variables (f : V 0 -> ZMod 2) :
    nonlinearity f = 0 := by
  have hfun : f = affineFunction 0 (f 0) := by
    funext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    unfold affineFunction
    change f 0 = f2Dot (0 : V 0) 0 + f 0
    have hdot : f2Dot (0 : V 0) 0 = 0 := by
      simp only [f2Dot, Finset.univ_eq_empty, Finset.sum_empty]
    rw [hdot, zero_add]
  have hdistance : hammingDistance f (affineFunction 0 (f 0)) = 0 := by
    unfold hammingDistance
    have hpoint :
        (fun x => f x + affineFunction 0 (f 0) x) =
          (fun _ => (0 : ZMod 2)) := by
      funext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      unfold affineFunction
      change f 0 + (f2Dot (0 : V 0) 0 + f 0) = 0
      have hdot : f2Dot (0 : V 0) 0 = 0 := by
        simp only [f2Dot, Finset.univ_eq_empty, Finset.sum_empty]
      rw [hdot, zero_add, CharTwo.add_self_eq_zero]
    rw [hpoint]
    simp
  have hle := nonlinearity_le_affine_distance f 0 (f 0)
  rw [hdistance] at hle
  exact Nat.eq_zero_of_le_zero hle

end LeanCipher.BooleanNonlinearity

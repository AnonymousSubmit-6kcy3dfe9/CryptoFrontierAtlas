import LeanCipher.BooleanWalsh
import LeanCipher.BooleanNonlinearity
import Mathlib

open scoped BigOperators

namespace LeanCipher.VectorialNonlinearity

open LeanCipher.BooleanWalsh

/-!
The component nonlinearity of a vectorial Boolean function, expressed through
its largest Walsh coefficient.  The zero component is deliberately excluded.
For an empty output space the filtered supremum is `0`, which merely makes the
spectral definition total.  The mathematical minimum-component semantics is
stated with `0 < m`; the paper's main theorem has `k < m`, so this condition
always holds there.
-/

def maximumWalshMagnitude (F : V n -> V m) : Nat :=
  ((Finset.univ : Finset (V m)).filter fun v => Not (v = 0)).sup fun v =>
    (Finset.univ : Finset (V n)).sup fun a =>
      (walsh (component F v) a).natAbs

def nonlinearity (F : V n -> V m) : Nat :=
  (2 ^ n - maximumWalshMagnitude F) / 2

def componentNonlinearities (F : V n -> V m) : Finset Nat :=
  ((Finset.univ : Finset (V m)).filter fun v => v ≠ 0).image
    (fun v => LeanCipher.BooleanNonlinearity.nonlinearity (component F v))

private theorem basisVector_ne_zero_of_pos {m : Nat} (hm : 0 < m) :
    (basisVector (⟨0, hm⟩ : Fin m) : V m) ≠ 0 := by
  intro h
  have h0 := congrFun h (⟨0, hm⟩ : Fin m)
  simp [basisVector] at h0

theorem componentNonlinearities_nonempty
    (F : V n -> V m) (hm : 0 < m) :
    (componentNonlinearities F).Nonempty := by
  refine ⟨LeanCipher.BooleanNonlinearity.nonlinearity
    (component F (basisVector (⟨0, hm⟩ : Fin m))), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨basisVector (⟨0, hm⟩ : Fin m), by
    simp [basisVector_ne_zero_of_pos hm], rfl⟩

def minComponentNonlinearity (F : V n -> V m) (hm : 0 < m) : Nat :=
  (componentNonlinearities F).min'
    (componentNonlinearities_nonempty F hm)

theorem minComponentNonlinearity_le
    (F : V n -> V m) (hm : 0 < m)
    {v : V m} (hv : v ≠ 0) :
    minComponentNonlinearity F hm ≤
      LeanCipher.BooleanNonlinearity.nonlinearity (component F v) := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨v, by simp [hv], rfl⟩

theorem exists_minComponentNonlinearity
    (F : V n -> V m) (hm : 0 < m) :
    ∃ v : V m, v ≠ 0 ∧
      LeanCipher.BooleanNonlinearity.nonlinearity (component F v) =
        minComponentNonlinearity F hm := by
  have hd := Finset.min'_mem (componentNonlinearities F)
    (componentNonlinearities_nonempty F hm)
  obtain ⟨v, hv, hvalue⟩ := Finset.mem_image.mp hd
  exact ⟨v, (Finset.mem_filter.mp hv).2, hvalue⟩

theorem nonlinearity_eq_scalar_component_min
    (F : V n -> V m) (hm : 0 < m) :
    nonlinearity F = minComponentNonlinearity F hm := by
  classical
  let S : Finset (V m) := Finset.univ.filter (fun v : V m => v ≠ 0)
  have hS : S.Nonempty := by
    refine ⟨basisVector (⟨0, hm⟩ : Fin m), ?_⟩
    simp [S, basisVector_ne_zero_of_pos hm]
  have hmaxEq :
      maximumWalshMagnitude F =
        S.sup (fun v =>
          (Finset.univ : Finset (V n)).sup fun a =>
            (walsh (component F v) a).natAbs) := rfl
  have hformula (v : V m) (hv : v ∈ S) :
      LeanCipher.BooleanNonlinearity.nonlinearity (component F v) =
        (2 ^ n -
          (Finset.univ : Finset (V n)).sup fun a =>
            (walsh (component F v) a).natAbs) / 2 := rfl
  have hmem (v : V m) (hv : v ∈ S) :
      LeanCipher.BooleanNonlinearity.nonlinearity (component F v) ∈
        componentNonlinearities F := by
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hmin_le (v : V m) (hv : v ∈ S) :
      minComponentNonlinearity F hm ≤
        LeanCipher.BooleanNonlinearity.nonlinearity (component F v) :=
    Finset.min'_le _ _ (hmem v hv)
  have hle : nonlinearity F ≤ minComponentNonlinearity F hm := by
    apply Finset.le_min'
    intro d hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
    rw [hformula v hv]
    apply Nat.div_le_div_right
    exact Nat.sub_le_sub_left (Finset.le_sup hv) _
  have hge : minComponentNonlinearity F hm ≤ nonlinearity F := by
    obtain ⟨v, hv, hvmax⟩ := Finset.exists_mem_eq_sup S hS
      (fun w => (Finset.univ : Finset (V n)).sup fun a =>
        (walsh (component F w) a).natAbs)
    have hmin := hmin_le v hv
    unfold nonlinearity
    rw [hmaxEq, hvmax, ← hformula v hv]
    exact hmin
  exact Nat.le_antisymm hle hge

theorem walsh_natAbs_le_maximum
    (F : V n -> V m) (v : V m) (a : V n) (hv : Not (v = 0)) :
    (walsh (component F v) a).natAbs <= maximumWalshMagnitude F := by
  apply le_trans (Finset.le_sup (s := (Finset.univ : Finset (V n)))
    (f := fun b => (walsh (component F v) b).natAbs) (Finset.mem_univ a))
  exact Finset.le_sup (s := (Finset.univ : Finset (V m)).filter fun w => Not (w = 0))
    (f := fun w => (Finset.univ : Finset (V n)).sup fun b =>
      (walsh (component F w) b).natAbs) (by simp [hv])

theorem two_dvd_walsh (f : V n -> ZMod 2) (a : V n) (hn : 1 <= n) :
    (2 : Int) ∣ walsh f a :=
  LeanCipher.BooleanNonlinearity.two_dvd_walsh f a hn

theorem two_dvd_abs_walsh (f : V n -> ZMod 2) (a : V n) (hn : 1 <= n) :
    (2 : Int) ∣ |walsh f a| := by
  exact (dvd_abs (2 : Int) (walsh f a)).mpr (two_dvd_walsh f a hn)

theorem walsh_abs_le_next_even
    (f : V (2 * k) -> ZMod 2) (a : V (2 * k)) (hk : 1 <= k)
    (h : |walsh f a| < ((2 ^ k + 4 : Nat) : Int)) :
    |walsh f a| <= ((2 ^ k + 2 : Nat) : Int) := by
  obtain ⟨q, hq⟩ : ∃ q : Int, (2 : Int) ^ k = 2 * q := by
    refine ⟨(2 : Int) ^ (k - 1), ?_⟩
    calc
      (2 : Int) ^ k = 2 ^ (1 + (k - 1)) := by congr 1; omega
      _ = 2 * (2 : Int) ^ (k - 1) := by rw [pow_add]; norm_num
  obtain ⟨z, hz⟩ := two_dvd_abs_walsh f a (by omega : 1 <= 2 * k)
  have habs : 0 <= |walsh f a| := abs_nonneg _
  push_cast at h ⊢
  rw [hq, hz] at h ⊢
  omega

theorem nonlinearity_le_of_walsh_witness
    (F : V n -> V m) (v : V m) (a : V n) (hv : Not (v = 0))
    (threshold : Nat)
    (hlarge : threshold <= (walsh (component F v) a).natAbs) :
    nonlinearity F <= (2 ^ n - threshold) / 2 := by
  have hmax : threshold <= maximumWalshMagnitude F :=
    hlarge.trans (walsh_natAbs_le_maximum F v a hv)
  unfold nonlinearity
  exact Nat.div_le_div_right (Nat.sub_le_sub_left hmax (2 ^ n))

theorem nonlinearity_le_main_bound_of_walsh_witness
    (F : V (2 * k) -> V m) (hk : 1 <= k)
    (v : V m) (a : V (2 * k)) (hv : Not (v = 0))
    (hlarge : 2 ^ k + 4 <= (walsh (component F v) a).natAbs) :
    nonlinearity F <= 2 ^ (2 * k - 1) - 2 ^ (k - 1) - 2 := by
  have h := nonlinearity_le_of_walsh_witness F v a hv (2 ^ k + 4) hlarge
  have hpow : 2 ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    calc
      2 ^ (2 * k) = 2 ^ (1 + (2 * k - 1)) := by congr 1; omega
      _ = 2 * 2 ^ (2 * k - 1) := by rw [pow_add]; norm_num
  have hkhalf : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ (1 + (k - 1)) := by congr 1; omega
      _ = 2 * 2 ^ (k - 1) := by rw [pow_add]; norm_num
  have hbound : 2 ^ k + 4 <= 2 ^ (2 * k) := by
    exact hlarge.trans
      (LeanCipher.BooleanNonlinearity.walsh_natAbs_le_card
        (component F v) a)
  have hcalc : (2 ^ (2 * k) - (2 ^ k + 4)) / 2 =
      2 ^ (2 * k - 1) - 2 ^ (k - 1) - 2 := by
    have hdiv : 2 ∣ 2 ^ (2 * k) - (2 ^ k + 4) := by
      refine ⟨2 ^ (2 * k - 1) - 2 ^ (k - 1) - 2, ?_⟩
      omega
    apply (Nat.div_eq_iff_eq_mul_left (a := 2 ^ (2 * k) - (2 ^ k + 4))
      (b := 2) (c := 2 ^ (2 * k - 1) - 2 ^ (k - 1) - 2)
      (by norm_num) hdiv).2
    omega
  rw [hcalc] at h
  exact h

theorem nonlinearity_le_main_bound_of_intAbs_witness
    (F : V (2 * k) -> V m) (hk : 1 <= k)
    (v : V m) (a : V (2 * k)) (hv : Not (v = 0))
    (hlarge : ((2 ^ k + 4 : Nat) : Int) <= |walsh (component F v) a|) :
    nonlinearity F <= 2 ^ (2 * k - 1) - 2 ^ (k - 1) - 2 := by
  apply nonlinearity_le_main_bound_of_walsh_witness F hk v a hv
  rw [← Int.natCast_natAbs] at hlarge
  exact_mod_cast hlarge

end LeanCipher.VectorialNonlinearity

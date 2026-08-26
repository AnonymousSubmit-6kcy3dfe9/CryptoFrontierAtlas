import LeanCipher.BalancedEightTerminal
import LeanCipher.BalancedEightCommonQuadratic
import LeanCipher.BalancedEightSliceArithmetic
import LeanCipher.BalancedEightEnumerationSound
import Mathlib

open scoped BigOperators

namespace LeanCipher.BalancedEightSemanticScalar

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

open LeanCipher.BooleanWalsh
open LeanCipher.BalancedEight
open LeanCipher.BalancedEightCertificates
open LeanCipher.BalancedEightRM
open LeanCipher.BalancedEightSliceArithmetic
open LeanCipher.BalancedEightCommonQuadratic

abbrev Vec := V 7

theorem local_weight_allowed
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    directionWeight f ell = 59 ∨ directionWeight f ell = 61 ∨
      directionWeight f ell = 63 :=
  directionWeight_mem f hf hnorm hall ell

theorem local_table_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    tableSum (localTable f ell) = 128 :=
  LeanCipher.BalancedEight.localTable_sum f hf hnorm hall ell

theorem oriented_slice_weights_odd
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    Odd (weight (orientedLowerSlice f ell)) ∧
      Odd (weight (orientedUpperSlice f ell)) := by
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h
  · rw [h.2.1, h.2.2]
    norm_num
  · rw [h.2.1, h.2.2]
    norm_num
  · rw [h.2.1, h.2.2]
    norm_num

private theorem evenMagnitude_zero
    (f : V 8 -> ZMod 2) (hf : weight f = 128) :
    evenMagnitude f 0 = 0 := by
  have hjoin : join (0 : Vec) 0 = (0 : V 8) := by
    decide
  rw [evenMagnitude, hjoin, walsh_zero_of_balanced f hf]
  norm_num

private theorem distinguished_cell_positive
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (ell : Vec) (m : Nat) (hm : oddMagnitude f ell = m) :
    0 < localCellCount f ell m 0 := by
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp [hm, evenMagnitude_zero f hf]

theorem local_distinguished_positive
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    0 < distinguishedCount (directionWeight f ell) (localTable f ell) := by
  rcases oriented_slice_weights f hf hnorm hall ell with h | h | h
  · simpa [distinguishedCount, directionWeight, localTable, h.2.1] using
      distinguished_cell_positive f hf ell 20 h.1
  · simpa [distinguishedCount, directionWeight, localTable, h.2.1] using
      distinguished_cell_positive f hf ell 12 h.1
  · simpa [distinguishedCount, directionWeight, localTable, h.2.1] using
      distinguished_cell_positive f hf ell 4 h.1

private theorem weight_indicator_eq_magnitudeCount
    (f : V 8 -> ZMod 2)
    (v : Vec -> ZMod 2)
    (hv : forall a, v a = if evenMagnitude f a = 8 then 1 else 0) :
    weight v = magnitudeCount (evenMagnitude f) 8 := by
  classical
  unfold weight magnitudeCount
  congr 1
  ext a
  simp [hv a]

theorem local_product_first_bit_weight
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    (localTable f ell).b + (localTable f ell).f +
        (localTable f ell).h ∈ quadraticWeights := by
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have hodd := oriented_slice_weights_odd f hf hnorm hall ell
  have hsum : forall a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a := by
    intro a
    exact oriented_normalized_sum_divisible_by_four
      f hf hnorm hall ell a
  obtain ⟨Q, linear, constant, hrepresentation, hquadraticWeight⟩ :=
    productFirstBit_quadratic_and_weight_mem g h hodd.1 hodd.2 hsum
  have hproduct : forall a : Vec,
      intParity (productFirstBit g h) a =
        if evenMagnitude f a = 8 then 1 else 0 := by
    intro a
    exact product_first_bit_eq_even_magnitude_indicator
      f hf hnorm hall ell a
  have hweight :
      weight (intParity (productFirstBit g h)) =
        magnitudeCount (evenMagnitude f) 8 :=
    weight_indicator_eq_magnitudeCount f _ hproduct
  have hcolumn := localTable_column_count f hf hnorm hall ell 8
  change
    (localTable f ell).b + (localTable f ell).f +
      (localTable f ell).h = magnitudeCount (evenMagnitude f) 8 at hcolumn
  rw [hcolumn, ← hweight]
  simpa [quadraticWeights, quadraticWeightSet] using hquadraticWeight

/-! ## Uniform local-table sum bridge -/

def localCellWeight
    (ca cb cc cd ce cf cg ch ci : Int) (odd even : Nat) : Int :=
  if odd = 20 ∧ even = 16 then ca
  else if odd = 20 ∧ even = 8 then cb
  else if odd = 12 ∧ even = 16 then cc
  else if odd = 20 ∧ even = 0 then cd
  else if odd = 4 ∧ even = 16 then ce
  else if odd = 12 ∧ even = 8 then cf
  else if odd = 12 ∧ even = 0 then cg
  else if odd = 4 ∧ even = 8 then ch
  else if odd = 4 ∧ even = 0 then ci
  else 0

def weightedTableValue
    (ca cb cc cd ce cf cg ch ci : Int) (t : LocalTable) : Int :=
  ca * (t.a : Int) + cb * (t.b : Int) + cc * (t.c : Int) +
    cd * (t.d : Int) + ce * (t.e : Int) + cf * (t.f : Int) +
    cg * (t.g : Int) + ch * (t.h : Int) + ci * (t.i : Int)

theorem localCellCount_cast_eq_sum_indicator
    (f : V 8 -> ZMod 2) (ell : Vec) (odd even : Nat) :
    (localCellCount f ell odd even : Int) =
      ∑ a : Vec,
        if oddMagnitude f (a + ell) = odd ∧ evenMagnitude f a = even
        then (1 : Int) else 0 := by
  simp [localCellCount, Finset.sum_boole]

theorem weightedLocalTable_eq_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) (ca cb cc cd ce cf cg ch ci : Int) :
    weightedTableValue ca cb cc cd ce cf cg ch ci (localTable f ell) =
      ∑ a : Vec, localCellWeight ca cb cc cd ce cf cg ch ci
        (oddMagnitude f (a + ell)) (evenMagnitude f a) := by
  simp only [weightedTableValue, localTable]
  rw [localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator,
    localCellCount_cast_eq_sum_indicator]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
      ho | ho | ho <;>
    rcases normalized_even_frequency_magnitude f hf hnorm hall a with
      he | he | he <;>
    simp [localCellWeight, oddMagnitude, evenMagnitude, ho, he]

/-! ## The combined second moment -/

theorem evenMagnitude_eq_normalized_sum
    (f : V 8 -> ZMod 2) (ell a : Vec) :
    evenMagnitude f a = 2 *
      (normalizedWalsh (orientedLowerSlice f ell) a +
        normalizedWalsh (orientedUpperSlice f ell) a).natAbs := by
  have hsum := oriented_slice_sum f ell a
  have hl := two_mul_normalizedWalsh (orientedLowerSlice f ell) a
  have hu := two_mul_normalizedWalsh (orientedUpperSlice f ell) a
  unfold evenMagnitude
  rw [hsum, ← hl, ← hu]
  rw [show 2 * normalizedWalsh (orientedLowerSlice f ell) a +
      2 * normalizedWalsh (orientedUpperSlice f ell) a =
      2 * (normalizedWalsh (orientedLowerSlice f ell) a +
        normalizedWalsh (orientedUpperSlice f ell) a) by ring]
  simp [Int.natAbs_mul]

theorem oddMagnitude_eq_normalized_difference
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell a : Vec) :
    oddMagnitude f (a + ell) = 2 *
      (normalizedWalsh (orientedLowerSlice f ell) a -
        normalizedWalsh (orientedUpperSlice f ell) a).natAbs := by
  have hne := normalized_odd_frequency_ne_zero f hf hnorm hall (a + ell)
  have hdiff := oriented_slice_difference_abs f ell a hne
  have hl := two_mul_normalizedWalsh (orientedLowerSlice f ell) a
  have hu := two_mul_normalizedWalsh (orientedUpperSlice f ell) a
  rw [← hl, ← hu] at hdiff
  rw [show 2 * normalizedWalsh (orientedLowerSlice f ell) a -
      2 * normalizedWalsh (orientedUpperSlice f ell) a =
      2 * (normalizedWalsh (orientedLowerSlice f ell) a -
        normalizedWalsh (orientedUpperSlice f ell) a) by ring] at hdiff
  simp only [Int.natAbs_mul] at hdiff
  norm_num at hdiff
  exact hdiff.symm

private theorem pair_second_scaled
    {p q : Int} {even odd : Nat}
    (heq : even = 2 * (p + q).natAbs)
    (hoq : odd = 2 * (p - q).natAbs) :
    8 * (p ^ 2 + q ^ 2) = (even : Int) ^ 2 + (odd : Int) ^ 2 := by
  have heqInt : (even : Int) = 2 * ((p + q).natAbs : Int) := by
    exact_mod_cast heq
  have hoqInt : (odd : Int) = 2 * ((p - q).natAbs : Int) := by
    exact_mod_cast hoq
  calc
    8 * (p ^ 2 + q ^ 2) =
        4 * ((p + q).natAbs : Int) ^ 2 +
          4 * ((p - q).natAbs : Int) ^ 2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]
      ring
    _ = (even : Int) ^ 2 + (odd : Int) ^ 2 := by
      rw [heqInt, hoqInt]
      ring

theorem local_secondMoment_as_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    (secondMoment (localTable f ell) : Int) =
      ∑ a : Vec,
        ((normalizedWalsh (orientedLowerSlice f ell) a) ^ 2 +
          (normalizedWalsh (orientedUpperSlice f ell) a) ^ 2) := by
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have htable := weightedLocalTable_eq_sum f hf hnorm hall ell
    82 58 50 50 34 26 18 10 2
  have hpoint (a : Vec) :
      localCellWeight 82 58 50 50 34 26 18 10 2
          (oddMagnitude f (a + ell)) (evenMagnitude f a) =
        normalizedWalsh g a ^ 2 + normalizedWalsh h a ^ 2 := by
    have hscaled := pair_second_scaled
      (evenMagnitude_eq_normalized_sum f ell a)
      (oddMagnitude_eq_normalized_difference f hf hnorm hall ell a)
    rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
        ho | ho | ho <;>
      rcases normalized_even_frequency_magnitude f hf hnorm hall a with
        he | he | he <;>
      norm_num [localCellWeight, oddMagnitude, evenMagnitude,
        g, h, ho, he] at hscaled ⊢ <;> omega
  calc
    (secondMoment (localTable f ell) : Int) =
        weightedTableValue 82 58 50 50 34 26 18 10 2
          (localTable f ell) := by
      norm_num [secondMoment, weightedTableValue]
    _ = ∑ a : Vec, localCellWeight 82 58 50 50 34 26 18 10 2
          (oddMagnitude f (a + ell)) (evenMagnitude f a) := htable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a

theorem local_combined_second_moment
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    secondMoment (localTable f ell) = 8192 := by
  have hsum := local_secondMoment_as_sum f hf hnorm hall ell
  rw [Finset.sum_add_distrib,
    normalizedWalsh_parseval, normalizedWalsh_parseval] at hsum
  norm_num at hsum
  exact_mod_cast hsum

/-! ## Product first-bit transform divisibility -/

private theorem pair_product_scaled
    {p q : Int} {even odd : Nat}
    (heq : even = 2 * (p + q).natAbs)
    (hoq : odd = 2 * (p - q).natAbs) :
    16 * (p * q) = (even : Int) ^ 2 - (odd : Int) ^ 2 := by
  have heqInt : (even : Int) = 2 * ((p + q).natAbs : Int) := by
    exact_mod_cast heq
  have hoqInt : (odd : Int) = 2 * ((p - q).natAbs : Int) := by
    exact_mod_cast hoq
  calc
    16 * (p * q) =
        4 * ((p + q).natAbs : Int) ^ 2 -
          4 * ((p - q).natAbs : Int) ^ 2 := by
      rw [Int.natAbs_sq, Int.natAbs_sq]
      ring
    _ = (even : Int) ^ 2 - (odd : Int) ^ 2 := by
      rw [heqInt, hoqInt]
      ring

theorem local_signedMoment_as_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    signedMoment (localTable f ell) =
      ∑ a : Vec, productFirstBit
        (orientedLowerSlice f ell) (orientedUpperSlice f ell) a := by
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have hodd := oriented_slice_weights_odd f hf hnorm hall ell
  have hsum : forall a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a := by
    intro a
    exact oriented_normalized_sum_divisible_by_four
      f hf hnorm hall ell a
  have htable := weightedLocalTable_eq_sum f hf hnorm hall ell
    (-2) (-5) 2 (-6) 4 (-1) (-2) 1 0
  have hpoint (a : Vec) :
      localCellWeight (-2) (-5) 2 (-6) 4 (-1) (-2) 1 0
          (oddMagnitude f (a + ell)) (evenMagnitude f a) =
        productFirstBit g h a := by
    have hpair := pair_product_scaled
      (evenMagnitude_eq_normalized_sum f ell a)
      (oddMagnitude_eq_normalized_difference f hf hnorm hall ell a)
    have hpair' :
        16 * (normalizedWalsh g a * normalizedWalsh h a) =
          (evenMagnitude f a : Int) ^ 2 -
            (oddMagnitude f (a + ell) : Int) ^ 2 := by
      simpa [g, h] using hpair
    have hfirstBit := four_mul_productFirstBit g h hodd.1 hsum a
    have hscaled :
        64 * productFirstBit g h a =
          (evenMagnitude f a : Int) ^ 2 -
            (oddMagnitude f (a + ell) : Int) ^ 2 + 16 := by
      calc
        64 * productFirstBit g h a =
            16 * (4 * productFirstBit g h a) := by ring
        _ = 16 *
            (normalizedWalsh g a * normalizedWalsh h a + 1) := by
          rw [hfirstBit]
        _ = 16 * (normalizedWalsh g a * normalizedWalsh h a) + 16 := by
          ring
        _ = _ := by rw [hpair']
    rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
        ho | ho | ho <;>
      rcases normalized_even_frequency_magnitude f hf hnorm hall a with
        he | he | he <;>
      norm_num [localCellWeight, oddMagnitude, evenMagnitude,
        g, h, ho, he] at hscaled ⊢ <;> omega
  calc
    signedMoment (localTable f ell) =
        weightedTableValue (-2) (-5) 2 (-6) 4 (-1) (-2) 1 0
          (localTable f ell) := by
      norm_num [signedMoment, weightedTableValue]
      ring
    _ = ∑ a : Vec, localCellWeight (-2) (-5) 2 (-6) 4 (-1) (-2) 1 0
          (oddMagnitude f (a + ell)) (evenMagnitude f a) := htable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a

theorem local_product_transform_divisible
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    signedMoment (localTable f ell) % 32 = 0 := by
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have hodd := oriented_slice_weights_odd f hf hnorm hall ell
  have hsum : forall a : Vec,
      (4 : Int) ∣ normalizedWalsh g a + normalizedWalsh h a := by
    intro a
    exact oriented_normalized_sum_divisible_by_four
      f hf hnorm hall ell a
  have hdiv := thirtyTwo_dvd_hadamard_productFirstBit
    g h hodd.1 hodd.2 hsum (0 : Vec)
  have hdivSum :
      (32 : Int) ∣ ∑ a : Vec, productFirstBit g h a := by
    simpa [hadamardTransform] using hdiv
  have hsigned := local_signedMoment_as_sum f hf hnorm hall ell
  change signedMoment (localTable f ell) = ∑ a : Vec, productFirstBit g h a
    at hsigned
  rw [← hsigned] at hdivSum
  obtain ⟨k, hk⟩ := hdivSum
  rw [hk]
  omega

/-! ## The combined fourth-moment congruence -/

private theorem pair_fourth_scaled
    {p q : Int} {even odd : Nat}
    (heq : even = 2 * (p + q).natAbs)
    (hoq : odd = 2 * (p - q).natAbs) :
    128 * (p ^ 4 + q ^ 4) =
      (even : Int) ^ 4 +
        6 * (even : Int) ^ 2 * (odd : Int) ^ 2 + (odd : Int) ^ 4 := by
  have heqInt : (even : Int) = 2 * ((p + q).natAbs : Int) := by
    exact_mod_cast heq
  have hoqInt : (odd : Int) = 2 * ((p - q).natAbs : Int) := by
    exact_mod_cast hoq
  have hplus : ((p + q).natAbs : Int) ^ 2 = (p + q) ^ 2 :=
    Int.natAbs_sq (p + q)
  have hminus : ((p - q).natAbs : Int) ^ 2 = (p - q) ^ 2 :=
    Int.natAbs_sq (p - q)
  calc
    128 * (p ^ 4 + q ^ 4) =
        16 * (((p + q).natAbs : Int) ^ 2) ^ 2 +
          96 * (((p + q).natAbs : Int) ^ 2) *
            (((p - q).natAbs : Int) ^ 2) +
          16 * (((p - q).natAbs : Int) ^ 2) ^ 2 := by
      rw [hplus, hminus]
      ring
    _ = (even : Int) ^ 4 +
        6 * (even : Int) ^ 2 * (odd : Int) ^ 2 +
          (odd : Int) ^ 4 := by
      rw [heqInt, hoqInt]
      ring

theorem local_fourthMoment_as_sum
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    (fourthMoment (localTable f ell) : Int) =
      ∑ a : Vec,
        ((normalizedWalsh (orientedLowerSlice f ell) a) ^ 4 +
          (normalizedWalsh (orientedUpperSlice f ell) a) ^ 4) := by
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have htable := weightedLocalTable_eq_sum f hf hnorm hall ell
    6562 2482 2402 1250 706 626 162 82 2
  have hpoint (a : Vec) :
      localCellWeight 6562 2482 2402 1250 706 626 162 82 2
          (oddMagnitude f (a + ell)) (evenMagnitude f a) =
        normalizedWalsh g a ^ 4 + normalizedWalsh h a ^ 4 := by
    have hscaled := pair_fourth_scaled
      (evenMagnitude_eq_normalized_sum f ell a)
      (oddMagnitude_eq_normalized_difference f hf hnorm hall ell a)
    rcases normalized_odd_frequency_magnitude f hf hnorm hall (a + ell) with
        ho | ho | ho <;>
      rcases normalized_even_frequency_magnitude f hf hnorm hall a with
        he | he | he <;>
      norm_num [localCellWeight, oddMagnitude, evenMagnitude,
        g, h, ho, he] at hscaled ⊢ <;> omega
  calc
    (fourthMoment (localTable f ell) : Int) =
        weightedTableValue 6562 2482 2402 1250 706 626 162 82 2
          (localTable f ell) := by
      norm_num [fourthMoment, weightedTableValue]
    _ = ∑ a : Vec,
        localCellWeight 6562 2482 2402 1250 706 626 162 82 2
          (oddMagnitude f (a + ell)) (evenMagnitude f a) := htable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a

theorem local_combined_fourth_congruence
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    fourthMoment (localTable f ell) % 1024 = 768 := by
  let g := orientedLowerSlice f ell
  let h := orientedUpperSlice f ell
  have hodd := oriented_slice_weights_odd f hf hnorm hall ell
  have hsum := local_fourthMoment_as_sum f hf hnorm hall ell
  change (fourthMoment (localTable f ell) : Int) =
      ∑ a : Vec, (normalizedWalsh g a ^ 4 + normalizedWalsh h a ^ 4)
    at hsum
  have hg := normalizedWalsh_fourth_moment_mod g hodd.1
  have hh := normalizedWalsh_fourth_moment_mod h hodd.2
  have hmod : (fourthMoment (localTable f ell) : Int) % 1024 = 768 := by
    rw [hsum, Finset.sum_add_distrib, Int.add_emod, hg, hh]
    norm_num
  exact_mod_cast hmod

/-! ## Scalar semantic interface -/

theorem semantic_scalar_conditions
    (f : V 8 -> ZMod 2) (hf : weight f = 128)
    (hnorm : supportXor f = lastBasis)
    (hall : forall a : V 8, (walsh f a).natAbs <= 20)
    (ell : Vec) :
    (directionWeight f ell = 59 ∨ directionWeight f ell = 61 ∨
        directionWeight f ell = 63) ∧
      tableSum (localTable f ell) = 128 ∧
      0 < distinguishedCount (directionWeight f ell) (localTable f ell) ∧
      secondMoment (localTable f ell) = 8192 ∧
      ((localTable f ell).b + (localTable f ell).f +
        (localTable f ell).h ∈ quadraticWeights) ∧
      signedMoment (localTable f ell) % 32 = 0 ∧
      fourthMoment (localTable f ell) % 1024 = 768 := by
  exact ⟨local_weight_allowed f hf hnorm hall ell,
    local_table_sum f hf hnorm hall ell,
    local_distinguished_positive f hf hnorm hall ell,
    local_combined_second_moment f hf hnorm hall ell,
    local_product_first_bit_weight f hf hnorm hall ell,
    local_product_transform_divisible f hf hnorm hall ell,
    local_combined_fourth_congruence f hf hnorm hall ell⟩

end LeanCipher.BalancedEightSemanticScalar

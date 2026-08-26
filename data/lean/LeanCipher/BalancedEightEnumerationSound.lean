import LeanCipher.BalancedEightCertificateReplay
import Std.Data.HashMap.Lemmas

namespace LeanCipher.BalancedEightCertificates

/-!
# Mathematical completeness of the local-table enumerator

The executable enumerator is intentionally kept separate from the Fourier
arguments that produce its input.  `SemanticLocalConditions` is the boundary:
it states the exact integer identities used in the paper, including an
explicit orientation witness.  The final theorem in this file proves that
every table crossing this boundary occurs in the independently replayed list
of declared certificate entries.
-/

def secondMoment (t : LocalTable) : Nat :=
  82 * t.a + 58 * t.b + 50 * t.c + 50 * t.d + 34 * t.e +
    26 * t.f + 18 * t.g + 10 * t.h + 2 * t.i

def orientationEnergy
    (da db dc de df dh : Int) : Int :=
  80 * da + 40 * db + 48 * dc + 16 * de + 24 * df + 8 * dh

def orientationFourth
    (da db dc de df dh : Int) : Int :=
  6560 * da + 2320 * db + 2400 * dc + 544 * de + 624 * df + 80 * dh

def orientationScore
    (da db dc de df dh : Int) : Int :=
  8 * da - 4 * db - 8 * dc + 8 * de + 4 * df - 4 * dh

def orientationQuadraticTotal (t : LocalTable) : Int :=
  t.b + 2 * t.d + 2 * t.e + t.f + 2 * t.g + t.h

def orientationQuadraticDifference (db df dh : Int) : Int :=
  -db + df + dh

def firstOrientedQuadraticWeight
    (t : LocalTable) (db df dh : Int) : Int :=
  (orientationQuadraticTotal t + orientationQuadraticDifference db df dh) / 2

def secondOrientedQuadraticWeight
    (t : LocalTable) (db df dh : Int) : Int :=
  orientationQuadraticTotal t - firstOrientedQuadraticWeight t db df dh

def SignedOrientationTarget (t : LocalTable) (deltaScore : Int) : Prop :=
  (totalScore t = -128 ∧ deltaScore = 0) ∨
  (totalScore t = 0 ∧ deltaScore = -128) ∨
  (totalScore t = 0 ∧ deltaScore = 128) ∨
  (totalScore t = 128 ∧ deltaScore = 0)

def OrientationWitness (t : LocalTable) : Prop :=
  ∃ da db dc de df dh : Int,
    da ∈ deltas t.a ∧ db ∈ deltas t.b ∧ dc ∈ deltas t.c ∧
    de ∈ deltas t.e ∧ df ∈ deltas t.f ∧ dh ∈ deltas t.h ∧
    orientationEnergy da db dc de df dh = 0 ∧
    orientationFourth da db dc de df dh % 2048 =
      (1792 - (fourthMoment t : Int)) % 2048 ∧
    SignedOrientationTarget t (orientationScore da db dc de df dh) ∧
    (orientationQuadraticTotal t + orientationQuadraticDifference db df dh) % 2 = 0 ∧
    firstOrientedQuadraticWeight t db df dh ∈ quadraticWeightsInt ∧
    secondOrientedQuadraticWeight t db df dh ∈ quadraticWeightsInt

structure SemanticLocalConditions (weight : Nat) (t : LocalTable) : Prop where
  weight_allowed : weight = 59 ∨ weight = 61 ∨ weight = 63
  table_sum : tableSum t = 128
  distinguished_positive : 0 < distinguishedCount weight t
  extreme_le : t.a ≤ 76
  combined_second_moment : secondMoment t = 8192
  product_first_bit_weight : t.b + t.f + t.h ∈ quadraticWeights
  product_transform_divisible : signedMoment t % 32 = 0
  combined_fourth_congruence : fourthMoment t % 1024 = 768
  orientation : OrientationWitness t

theorem replacement_cost_of_sum_and_second_moment
    (t : LocalTable) (hsum : tableSum t = 128)
    (hsecond : secondMoment t = 8192) :
    t.c + t.d + 3 * t.e + 4 * t.f + 5 * t.g + 6 * t.h + 7 * t.i + 96 =
      3 * t.a := by
  unfold tableSum at hsum
  unfold secondMoment at hsecond
  omega

theorem second_oriented_quadratic_weight_eq_half_difference
    (t : LocalTable) (db df dh : Int)
    (heven :
      (orientationQuadraticTotal t + orientationQuadraticDifference db df dh) % 2 = 0) :
    secondOrientedQuadraticWeight t db df dh =
      (orientationQuadraticTotal t - orientationQuadraticDifference db df dh) / 2 := by
  unfold secondOrientedQuadraticWeight firstOrientedQuadraticWeight
  omega

private def Carries
    (map : Std.HashMap RightKey (List Int)) (key : RightKey) (value : Int) : Prop :=
  ∃ values, map.get? key = some values ∧ value ∈ values

private theorem addRight_carries_self
    (map : Std.HashMap RightKey (List Int)) (key : RightKey) (value : Int) :
    Carries (addRight map key value) key value := by
  refine ⟨value :: (map.get? key).getD [], ?_, by simp⟩
  simp [addRight, Std.HashMap.get?_eq_getElem?]

private theorem addRight_preserves_carries
    (map : Std.HashMap RightKey (List Int)) (newKey key : RightKey)
    (newValue value : Int) (h : Carries map key value) :
    Carries (addRight map newKey newValue) key value := by
  rcases h with ⟨values, hget, hmem⟩
  have hget' : map[key]? = some values := by
    simpa [Std.HashMap.get?_eq_getElem?] using hget
  by_cases hkey : newKey = key
  · subst newKey
    refine ⟨newValue :: values, ?_, by simp [hmem]⟩
    simp [addRight, Std.HashMap.get?_eq_getElem?, hget']
  · refine ⟨values, ?_, hmem⟩
    rw [show (addRight map newKey newValue).get? key =
        (map.insert newKey (newValue :: map[newKey]?.getD []))[key]? by rfl]
    rw [Std.HashMap.getElem?_insert]
    simp [hkey, hget']

private theorem foldl_preserves_carries
    {α : Type} (items : List α)
    (step : Std.HashMap RightKey (List Int) → α →
      Std.HashMap RightKey (List Int))
    (key : RightKey) (value : Int)
    (hstep : ∀ map item, Carries map key value → Carries (step map item) key value)
    (map : Std.HashMap RightKey (List Int)) (h : Carries map key value) :
    Carries (items.foldl step map) key value := by
  induction items generalizing map with
  | nil => exact h
  | cons item items ih =>
      exact ih (step map item) (hstep map item h)

private theorem foldl_carries_of_mem
    {α : Type} (items : List α) (chosen : α) (hchosen : chosen ∈ items)
    (step : Std.HashMap RightKey (List Int) → α →
      Std.HashMap RightKey (List Int))
    (key : RightKey) (value : Int)
    (hstep : ∀ map item, Carries map key value → Carries (step map item) key value)
    (hchosenStep : ∀ map, Carries (step map chosen) key value)
    (map : Std.HashMap RightKey (List Int)) :
    Carries (items.foldl step map) key value := by
  induction items generalizing map with
  | nil => simp at hchosen
  | cons item items ih =>
      by_cases hitem : item = chosen
      · subst item
        exact foldl_preserves_carries items step key value hstep
          (step map chosen) (hchosenStep map)
      · apply ih (map := step map item)
        simp only [List.mem_cons] at hchosen
        rcases hchosen with hEq | htail
        · exact False.elim (hitem hEq.symm)
        · exact htail

private def rightHBatch (t : LocalTable) (de df : Int)
    (map : Std.HashMap RightKey (List Int)) :
    Std.HashMap RightKey (List Int) :=
  (deltas t.h).foldl (fun map dh =>
    addRight map
      (16 * de + 24 * df + 8 * dh,
        (544 * de + 624 * df + 80 * dh) % 2048,
        8 * de + 4 * df - 4 * dh)
      (df + dh)) map

private def rightFBatch (t : LocalTable) (de : Int)
    (map : Std.HashMap RightKey (List Int)) :
    Std.HashMap RightKey (List Int) :=
  (deltas t.f).foldl (fun map df => rightHBatch t de df map) map

private def rightEBatch (t : LocalTable)
    (map : Std.HashMap RightKey (List Int)) :
    Std.HashMap RightKey (List Int) :=
  (deltas t.e).foldl (fun map de => rightFBatch t de map) map

private theorem rightIndex_eq_rightEBatch (t : LocalTable) :
    rightIndex t = rightEBatch t {} := by
  rfl

private theorem rightHBatch_preserves_carries
    (t : LocalTable) (de df : Int)
    (map : Std.HashMap RightKey (List Int)) (key : RightKey) (value : Int)
    (h : Carries map key value) :
    Carries (rightHBatch t de df map) key value := by
  unfold rightHBatch
  apply foldl_preserves_carries (deltas t.h) _ key value
  · intro current dh hcurrent
    exact addRight_preserves_carries current _ key _ value hcurrent
  · exact h

private theorem rightHBatch_carries
    (t : LocalTable) (de df dh : Int) (hdh : dh ∈ deltas t.h)
    (map : Std.HashMap RightKey (List Int)) :
    Carries (rightHBatch t de df map)
      (16 * de + 24 * df + 8 * dh,
        (544 * de + 624 * df + 80 * dh) % 2048,
        8 * de + 4 * df - 4 * dh)
      (df + dh) := by
  unfold rightHBatch
  apply foldl_carries_of_mem (deltas t.h) dh hdh _ _ _
  · intro current item hcurrent
    exact addRight_preserves_carries current _ _ _ _ hcurrent
  · intro current
    exact addRight_carries_self current _ _

private theorem rightFBatch_preserves_carries
    (t : LocalTable) (de : Int)
    (map : Std.HashMap RightKey (List Int)) (key : RightKey) (value : Int)
    (h : Carries map key value) :
    Carries (rightFBatch t de map) key value := by
  unfold rightFBatch
  apply foldl_preserves_carries (deltas t.f) _ key value
  · intro current df hcurrent
    exact rightHBatch_preserves_carries t de df current key value hcurrent
  · exact h

private theorem rightFBatch_carries
    (t : LocalTable) (de df dh : Int)
    (hdf : df ∈ deltas t.f) (hdh : dh ∈ deltas t.h)
    (map : Std.HashMap RightKey (List Int)) :
    Carries (rightFBatch t de map)
      (16 * de + 24 * df + 8 * dh,
        (544 * de + 624 * df + 80 * dh) % 2048,
        8 * de + 4 * df - 4 * dh)
      (df + dh) := by
  unfold rightFBatch
  apply foldl_carries_of_mem (deltas t.f) df hdf _ _ _
  · intro current item hcurrent
    exact rightHBatch_preserves_carries t de item current _ _ hcurrent
  · intro current
    exact rightHBatch_carries t de df dh hdh current

private theorem rightIndex_carries
    (t : LocalTable) (de df dh : Int)
    (hde : de ∈ deltas t.e) (hdf : df ∈ deltas t.f)
    (hdh : dh ∈ deltas t.h) :
    Carries (rightIndex t)
      (16 * de + 24 * df + 8 * dh,
        (544 * de + 624 * df + 80 * dh) % 2048,
        8 * de + 4 * df - 4 * dh)
      (df + dh) := by
  rw [rightIndex_eq_rightEBatch]
  unfold rightEBatch
  apply foldl_carries_of_mem (deltas t.e) de hde _ _ _
  · intro current item hcurrent
    exact rightFBatch_preserves_carries t item current _ _ hcurrent
  · intro current
    exact rightFBatch_carries t de df dh hdf hdh current

private theorem signedOrientationTarget_mem_scoreTargets
    (t : LocalTable) (deltaScore : Int)
    (h : SignedOrientationTarget t deltaScore) :
    deltaScore ∈ scoreTargets (totalScore t) := by
  rcases h with h | h | h | h
  · rcases h with ⟨hscore, hdelta⟩
    simp [scoreTargets, hscore, hdelta]
  · rcases h with ⟨hscore, hdelta⟩
    simp [scoreTargets, hscore, hdelta]
  · rcases h with ⟨hscore, hdelta⟩
    simp [scoreTargets, hscore, hdelta]
  · rcases h with ⟨hscore, hdelta⟩
    simp [scoreTargets, hscore, hdelta]

theorem orientationPossible_complete
    (t : LocalTable) (h : OrientationWitness t) :
    orientationPossible t (fourthMoment t) = true := by
  rcases h with
    ⟨da, db, dc, de, df, dh, hda, hdb, hdc, hde, hdf, hdh,
      henergy, hfourth, hsigned, heven, hq1, hq2⟩
  have htarget :
      orientationScore da db dc de df dh ∈ scoreTargets (totalScore t) :=
    signedOrientationTarget_mem_scoreTargets t _ hsigned
  have htargetsNonempty : (scoreTargets (totalScore t)).isEmpty = false :=
    List.isEmpty_eq_false_iff_exists_mem.mpr
      ⟨orientationScore da db dc de df dh, htarget⟩
  have hright := rightIndex_carries t de df dh hde hdf hdh
  rcases hright with ⟨differences, hget, hdifference⟩
  have hEnergyKey :
      -(80 * da + 40 * db + 48 * dc) =
        16 * de + 24 * df + 8 * dh := by
    unfold orientationEnergy at henergy
    omega
  have hFourthKey :
      ((1792 - (fourthMoment t : Int)) % 2048 -
          (6560 * da + 2320 * db + 2400 * dc) % 2048) % 2048 =
        (544 * de + 624 * df + 80 * dh) % 2048 := by
    unfold orientationFourth at hfourth
    omega
  have hScoreKey :
      orientationScore da db dc de df dh -
          (8 * da - 4 * db - 8 * dc) =
        8 * de + 4 * df - 4 * dh := by
    unfold orientationScore
    omega
  have hgetAlgorithm :
      (rightIndex t).get?
        (-(80 * da + 40 * db + 48 * dc),
          ((1792 - (fourthMoment t : Int)) % 2048 -
            (6560 * da + 2320 * db + 2400 * dc) % 2048) % 2048,
          orientationScore da db dc de df dh -
            (8 * da - 4 * db - 8 * dc)) = some differences := by
    rw [hEnergyKey, hFourthKey, hScoreKey]
    exact hget
  unfold orientationPossible
  dsimp only
  rw [htargetsNonempty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply List.any_eq_true.mpr
  refine ⟨da, hda, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨db, hdb, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨dc, hdc, ?_⟩
  dsimp only
  apply List.any_eq_true.mpr
  refine ⟨orientationScore da db dc de df dh, htarget, ?_⟩
  rw [hgetAlgorithm]
  apply List.any_eq_true.mpr
  refine ⟨df + dh, hdifference, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
  constructor
  · constructor
    · simpa [orientationQuadraticTotal, orientationQuadraticDifference,
        add_assoc] using heven
    · simpa [firstOrientedQuadraticWeight, orientationQuadraticTotal,
        orientationQuadraticDifference, add_assoc] using hq1
  · simpa [secondOrientedQuadraticWeight, firstOrientedQuadraticWeight,
      orientationQuadraticTotal, orientationQuadraticDifference, add_assoc] using hq2

theorem scalarFilters_complete
    (t : LocalTable)
    (hweight : t.b + t.f + t.h ∈ quadraticWeights)
    (hsigned : signedMoment t % 32 = 0)
    (hfourth : fourthMoment t % 1024 = 768) :
    scalarFilters t = some (fourthMoment t) := by
  simp [scalarFilters, hweight, hsigned, hfourth]

private theorem countsAt_complete_zero3
    (t : LocalTable) (hsum : tableSum t = 128)
    (hd : 0 < t.d)
    (hreplacement :
      t.c + t.d + 3 * t.e + 4 * t.f + 5 * t.g + 6 * t.h + 7 * t.i + 96 =
        3 * t.a) :
    t ∈ countsAt t.a 3 := by
  rcases t with ⟨a, b, c, d, e, f, g, h, i⟩
  simp only [tableSum] at hsum
  simp only at hd hreplacement
  simp [countsAt, zeroEnergy]
  omega

private theorem countsAt_complete_zero6
    (t : LocalTable) (hsum : tableSum t = 128)
    (hg : 0 < t.g)
    (hreplacement :
      t.c + t.d + 3 * t.e + 4 * t.f + 5 * t.g + 6 * t.h + 7 * t.i + 96 =
        3 * t.a) :
    t ∈ countsAt t.a 6 := by
  rcases t with ⟨a, b, c, d, e, f, g, h, i⟩
  simp only [tableSum] at hsum
  simp only at hg hreplacement
  have hn : ¬18 + 24 * a < 826 := by omega
  have htarget :
      (18 + 24 * a - 826) / 8 =
        c + d + 3 * e + 4 * f + 5 * (g - 1) + 6 * h + 7 * i := by
    omega
  simp [countsAt, zeroEnergy, hn, htarget]
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  refine ⟨g - 1, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  omega

private theorem countsAt_complete_zero8
    (t : LocalTable) (hsum : tableSum t = 128)
    (hi : 0 < t.i)
    (hreplacement :
      t.c + t.d + 3 * t.e + 4 * t.f + 5 * t.g + 6 * t.h + 7 * t.i + 96 =
        3 * t.a) :
    t ∈ countsAt t.a 8 := by
  rcases t with ⟨a, b, c, d, e, f, g, h, i⟩
  simp only [tableSum] at hsum
  simp only at hi hreplacement
  have hn : ¬2 + 24 * a < 826 := by omega
  have htarget :
      (2 + 24 * a - 826) / 8 =
        c + d + 3 * e + 4 * f + 5 * g + 6 * h + 7 * (i - 1) := by
    omega
  simp [countsAt, zeroEnergy, hn, htarget]
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  constructor
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  refine ⟨i - 1, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    omega
  omega

theorem countsAt_complete
    (weight : Nat) (t : LocalTable)
    (hweight : weight = 59 ∨ weight = 61 ∨ weight = 63)
    (hsum : tableSum t = 128)
    (hdistinguished : 0 < distinguishedCount weight t)
    (hsecond : secondMoment t = 8192) :
    t ∈ countsAt t.a (zeroType weight) := by
  have hreplacement := replacement_cost_of_sum_and_second_moment t hsum hsecond
  rcases hweight with rfl | rfl | rfl
  · simpa [zeroType] using
      countsAt_complete_zero3 t hsum (by simpa [distinguishedCount] using hdistinguished)
        hreplacement
  · simpa [zeroType] using
      countsAt_complete_zero6 t hsum (by simpa [distinguishedCount] using hdistinguished)
        hreplacement
  · simpa [zeroType] using
      countsAt_complete_zero8 t hsum (by simpa [distinguishedCount] using hdistinguished)
        hreplacement

theorem enumerateWeight_complete
    (weight : Nat) (t : LocalTable)
    (h : SemanticLocalConditions weight t) :
    (margins t, t) ∈ enumerateWeight weight := by
  rcases h with
    ⟨hweight, hsum, hdistinguished, hextreme, hsecond, hproductWeight,
      hproductDivisible, hfourth, horientation⟩
  have hcounts : t ∈ countsAt t.a (zeroType weight) :=
    countsAt_complete weight t hweight hsum hdistinguished hsecond
  have hscalar : scalarFilters t = some (fourthMoment t) :=
    scalarFilters_complete t hproductWeight hproductDivisible hfourth
  have horientationPossible :
      orientationPossible t (fourthMoment t) = true :=
    orientationPossible_complete t horientation
  unfold enumerateWeight
  apply List.mem_flatMap.mpr
  refine ⟨t.a, by simp; omega, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨t, hcounts, ?_⟩
  simp [hscalar, horientationPossible]

theorem generatedEntriesFor_complete
    (weight : Nat) (t : LocalTable)
    (h : SemanticLocalConditions weight t) :
    (weight, margins t, t) ∈ generatedEntriesFor weight := by
  apply List.mem_map.mpr
  exact ⟨(margins t, t), enumerateWeight_complete weight t h, rfl⟩

private theorem mem_of_canonicalEntries_eq
    (entry : TableEntry) (left right : List TableEntry)
    (hentry : entry ∈ left)
    (heq : canonicalEntries left = canonicalEntries right) :
    entry ∈ right := by
  have hcanonical : entry ∈ canonicalEntries left := by
    simpa [canonicalEntries] using hentry
  rw [heq] at hcanonical
  simpa [canonicalEntries] using hcanonical

private theorem declaredEntriesFor_subset_declaredEntries
    (weight : Nat) (entry : TableEntry)
    (hentry : entry ∈ declaredEntriesFor weight) :
    entry ∈ declaredEntries := by
  unfold declaredEntriesFor at hentry
  unfold declaredEntries
  rcases List.mem_flatMap.mp hentry with ⟨family, hfamily, hrow⟩
  exact List.mem_flatMap.mpr
    ⟨family, (List.mem_filter.mp hfamily).1, hrow⟩

theorem SemanticLocalConditions.mem_declaredEntriesFor
    {weight : Nat} {t : LocalTable}
    (h : SemanticLocalConditions weight t) :
    (weight, margins t, t) ∈ declaredEntriesFor weight := by
  have hgenerated := generatedEntriesFor_complete weight t h
  rcases h.weight_allowed with rfl | rfl | rfl
  · exact mem_of_canonicalEntries_eq _ _ _ hgenerated
      weight59_tables_generated_by_executable_enumerator
  · exact mem_of_canonicalEntries_eq _ _ _ hgenerated
      weight61_tables_generated_by_executable_enumerator
  · exact mem_of_canonicalEntries_eq _ _ _ hgenerated
      weight63_tables_generated_by_executable_enumerator

theorem SemanticLocalConditions.mem_declaredEntries
    {weight : Nat} {t : LocalTable}
    (h : SemanticLocalConditions weight t) :
    (weight, margins t, t) ∈ declaredEntries :=
  declaredEntriesFor_subset_declaredEntries weight _ h.mem_declaredEntriesFor

end LeanCipher.BalancedEightCertificates

import LeanCipher.TuDengCyclic
import LeanCipher.TuDengCube

open scoped BigOperators

namespace LeanCipher.TuDengPartition

open LeanCipher.TuDengCyclic
open LeanCipher.TuDengCube

variable {k : Nat} [NeZero k]

noncomputable def inputOfSet (s : Finset (ZMod k)) : InputWord k :=
  fun j => decide (j ∈ s)

omit [NeZero k] in
@[simp] theorem inputOfSet_eq_true {s : Finset (ZMod k)} {j : ZMod k} :
    inputOfSet s j = true ↔ j ∈ s := by
  simp [inputOfSet]

omit [NeZero k] in
@[simp] theorem inputOfSet_eq_false {s : Finset (ZMod k)} {j : ZMod k} :
    inputOfSet s j = false ↔ j ∉ s := by
  simp [inputOfSet]

noncomputable def setOfInput (x : InputWord k) : Finset (ZMod k) :=
  Finset.univ.filter fun j => x j = true

@[simp] theorem inputOfSet_setOfInput (x : InputWord k) :
    inputOfSet (setOfInput x) = x := by
  funext j
  cases hx : x j <;> simp [inputOfSet, setOfInput, hx]

@[simp] theorem setOfInput_inputOfSet (s : Finset (ZMod k)) :
    setOfInput (inputOfSet s) = s := by
  ext j
  simp [setOfInput]

noncomputable def carryOfSet (C : Finset (ZMod k)) : CarryWord k :=
  fun j => j ∈ C

@[simp] theorem carrySet_carryOfSet (C : Finset (ZMod k)) :
    carrySet (carryOfSet C) = C := by
  ext j
  simp [carrySet, carryOfSet]

@[simp] theorem carryOfSet_carrySet (c : CarryWord k) :
    carryOfSet (carrySet c) = c := by
  funext j
  apply propext
  simp [carryOfSet, carrySet]

noncomputable def propBadFamily (d : InputWord k) :
    Finset (Finset (ZMod k)) :=
  Finset.univ.filter fun s =>
    inputWeight d < weight (selectedCarry (inputOfSet s) d)

@[simp] theorem mem_propBadFamily {d : InputWord k} {s : Finset (ZMod k)} :
    s ∈ propBadFamily d ↔
      inputWeight d < weight (selectedCarry (inputOfSet s) d) := by
  simp [propBadFamily]

omit [NeZero k] in
theorem inputOfSet_mono {s t : Finset (ZMod k)} (hst : s ⊆ t) :
    ∀ j, (inputOfSet s j).toNat ≤ (inputOfSet t j).toNat := by
  intro j
  by_cases hj : j ∈ s
  · have hjt := hst hj
    simp [inputOfSet, hj, hjt]
  · simp [inputOfSet, hj]

theorem propBadFamily_increasing (d : InputWord k) :
    IsIncreasing (propBadFamily d) := by
  intro s t hst hs
  rw [mem_propBadFamily] at hs ⊢
  have hcarry := selectedCarry_mono (d := d) (inputOfSet_mono hst)
  have hcard := Finset.card_le_card (carrySet_mono hcarry)
  exact hs.trans_le hcard

omit [NeZero k] in
theorem inputOfSet_insert_isFlip {s : Finset (ZMod k)} {i : ZMod k}
    (hi : i ∉ s) :
    IsFlip (inputOfSet s) (inputOfSet (insert i s)) i := by
  refine ⟨?_, ?_, ?_⟩
  · simp [inputOfSet, hi]
  · simp [inputOfSet]
  · intro j hji
    simp [inputOfSet, hji]

def Group (k : Nat) := ZMod k × Finset (ZMod k)

noncomputable instance groupDecidableEq : DecidableEq (Group k) :=
  Classical.decEq _

noncomputable def edgeGroup (d : InputWord k) (i : ZMod k)
    (s : Finset (ZMod k)) : Group k :=
  (i, carrySet (selectedCarry (inputOfSet (insert i s)) d))

noncomputable def activeGroups (d : InputWord k) : Finset (Group k) := by
  classical
  exact ((((Finset.univ : Finset (ZMod k)).product
      (Finset.univ : Finset (Finset (ZMod k)))).filter fun e =>
    IsPivotal (propBadFamily d) e.1 e.2).image fun e => edgeGroup d e.1 e.2)

theorem mem_activeGroups_iff {d : InputWord k} {g : Group k} :
    g ∈ activeGroups d ↔ ∃ i s,
      IsPivotal (propBadFamily d) i s ∧ edgeGroup d i s = g := by
  classical
  constructor
  · intro hg
    rw [activeGroups] at hg
    obtain ⟨e, he, heg⟩ := Finset.mem_image.mp hg
    exact ⟨e.1, e.2, (Finset.mem_filter.mp he).2, heg⟩
  · rintro ⟨i, s, hpiv, hgroup⟩
    rw [activeGroups]
    apply Finset.mem_image.mpr
    refine ⟨(i, s), ?_, hgroup⟩
    exact Finset.mem_filter.mpr ⟨by simp, hpiv⟩

noncomputable def mismatchSet (d : InputWord k) (C : Finset (ZMod k)) :
    Finset (ZMod k) :=
  Finset.univ.filter fun j => ¬ (j ∈ C ↔ d j = true)

noncomputable def outgoingOneSet (d : InputWord k) (C : Finset (ZMod k)) :
    Finset (ZMod k) :=
  (mismatchSet d C).filter fun j => j + 1 ∈ C

noncomputable def forcedZeroSet (d : InputWord k) (i : ZMod k) (h : Nat) :
    Finset (ZMod k) :=
  ((Finset.range (h - 1)).image fun r => i + ((r + 1 : Nat) : ZMod k)).filter
    fun j => d j = true

noncomputable def fixedOnes (d : InputWord k) (g : Group k) :
    Finset (ZMod k) :=
  (outgoingOneSet d g.2).erase g.1

noncomputable def fixedZeros (d : InputWord k) (g : Group k) :
    Finset (ZMod k) :=
  (mismatchSet d g.2 \ outgoingOneSet d g.2) ∪
    forcedZeroSet d g.1 (g.2.card - inputWeight d)

theorem carry_weight_le_k (c : CarryWord k) : weight c ≤ k := by
  unfold weight
  calc
    (carrySet c).card ≤ (Finset.univ : Finset (ZMod k)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = k := by simp

theorem pivotal_edge_conditions
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {i : ZMod k} {s : Finset (ZMod k)}
    (hpiv : IsPivotal (propBadFamily d) i s) :
    let upper := inputOfSet (insert i s)
    let h := weight (selectedCarry upper d) - inputWeight d
    0 < h ∧ h < k ∧
      weight (selectedCarry upper d) = inputWeight d + h ∧
      PivotalConditions d upper (selectedCarry upper d) i h := by
  dsimp only
  rcases hpiv with ⟨hi, hslo, hshi⟩
  rw [mem_propBadFamily] at hshi
  have hlower : weight (selectedCarry (inputOfSet s) d) ≤ inputWeight d := by
    rw [mem_propBadFamily] at hslo
    omega
  let h := weight (selectedCarry (inputOfSet (insert i s)) d) - inputWeight d
  have hh : 0 < h := by dsimp [h]; omega
  have hsum : weight (selectedCarry (inputOfSet (insert i s)) d) =
      inputWeight d + h := by dsimp [h]; omega
  have hhk : h < k := by
    have hw := carry_weight_le_k (selectedCarry (inputOfSet (insert i s)) d)
    omega
  refine ⟨hh, hhk, hsum, ?_⟩
  exact pivotal_conditions_of_rank_crossing
    (inputOfSet_insert_isFlip hi) (inputWeight d) h hh hhk hsum hlower

theorem active_group_data
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    ∃ s, IsPivotal (propBadFamily d) g.1 s ∧
      carrySet (selectedCarry (inputOfSet (insert g.1 s)) d) = g.2 ∧
      let h := g.2.card - inputWeight d
      0 < h ∧ h < k ∧
        weight (carryOfSet g.2) = inputWeight d + h ∧
        CarryCompatible (inputOfSet (insert g.1 s)) d (carryOfSet g.2) ∧
        PivotalConditions d (inputOfSet (insert g.1 s))
          (carryOfSet g.2) g.1 h := by
  classical
  obtain ⟨i, s, hpiv, hgroup⟩ := mem_activeGroups_iff.mp hg
  have hi : i = g.1 := by
    simpa [edgeGroup] using congrArg Prod.fst hgroup
  subst i
  have hC : carrySet (selectedCarry (inputOfSet (insert g.1 s)) d) = g.2 := by
    simpa [edgeGroup] using congrArg Prod.snd hgroup
  refine ⟨s, hpiv, hC, ?_⟩
  have hdata := pivotal_edge_conditions hdpos hpiv
  dsimp only at hdata ⊢
  rw [← hC, carryOfSet_carrySet]
  exact And.intro hdata.1 (And.intro hdata.2.1
      (And.intro hdata.2.2.1
        (And.intro
          (selectedCarry_compatible (inputOfSet (insert g.1 s)) d)
          hdata.2.2.2)))

theorem active_group_support
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    ∀ j, (carryOfSet g.2 j ↔ d j = true) →
      (carryOfSet g.2 (j + 1) ↔ carryOfSet g.2 j) := by
  obtain ⟨s, _, _, _, _, _, hcompat, _⟩ := active_group_data hdpos hg
  intro j hmatch
  exact compatible_support hcompat hmatch

theorem compatible_active_group_iff
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d)
    (u : Finset (ZMod k)) :
    CarryCompatible (inputOfSet u) d (carryOfSet g.2) ↔
      ∀ j ∈ mismatchSet d g.2, (j ∈ u ↔ j + 1 ∈ g.2) := by
  rw [compatible_iff_of_support (active_group_support hdpos hg)]
  constructor
  · intro h j hj
    have hmis : ¬ (carryOfSet g.2 j ↔ d j = true) := by
      simpa [mismatchSet] using hj
    simpa [carryOfSet] using h j hmis
  · intro h j hmis
    have hj : j ∈ mismatchSet d g.2 := by
      simpa [mismatchSet, carryOfSet] using hmis
    simpa [carryOfSet] using h j hj

theorem selectedCarry_eq_active_of_compatible
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d)
    {x : InputWord k} (hx : CarryCompatible x d (carryOfSet g.2)) :
    carryOfSet g.2 = selectedCarry x d := by
  obtain ⟨_, _, _, hh, _, hweight, _, _⟩ := active_group_data hdpos hg
  apply compatible_bad_eq_selected hx
  rw [hweight]
  omega

theorem active_group_shape
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    let h := g.2.card - inputWeight d
    0 < h ∧ h < k ∧
      (¬ (g.1 ∈ g.2 ↔ d g.1 = true)) ∧
      (∀ r : Nat, 0 < r → r ≤ h →
        g.1 + (r : ZMod k) ∈ g.2) := by
  obtain ⟨_, _, _, hh, hhk, _, _, hcond⟩ := active_group_data hdpos hg
  dsimp only at hh hhk hcond ⊢
  refine ⟨hh, hhk, ?_, ?_⟩
  · simpa [carryOfSet] using hcond.1
  · intro r hr0 hrh
    simpa [carryOfSet] using hcond.2.1 r hr0 hrh

theorem active_flip_mem_outgoingOneSet
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    g.1 ∈ outgoingOneSet d g.2 := by
  have hshape := active_group_shape hdpos hg
  dsimp only at hshape
  have hnext := hshape.2.2.2 1 (by omega) (by omega)
  have hnext' : g.1 + 1 ∈ g.2 := by simpa using hnext
  simp [outgoingOneSet, mismatchSet, hshape.2.2.1, hnext']

omit [NeZero k] in
theorem mem_forcedZeroSet_of_position
    {d : InputWord k} {i : ZMod k} {h r : Nat}
    (hr0 : 0 < r) (hrh : r < h)
    (hd : d (i + (r : ZMod k)) = true) :
    i + (r : ZMod k) ∈ forcedZeroSet d i h := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, hd⟩
  apply Finset.mem_image.mpr
  refine ⟨r - 1, Finset.mem_range.mpr (by omega), ?_⟩
  congr 1
  norm_num [show r - 1 + 1 = r by omega]

omit [NeZero k] in
theorem forcedZeroSet_position
    {d : InputWord k} {i j : ZMod k} {h : Nat}
    (hj : j ∈ forcedZeroSet d i h) :
    ∃ r : Nat, 0 < r ∧ r < h ∧ j = i + (r : ZMod k) ∧ d j = true := by
  rcases Finset.mem_filter.mp hj with ⟨hjimage, hd⟩
  obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hjimage
  refine ⟨q + 1, by omega, ?_, ?_, hd⟩
  · have := Finset.mem_range.mp hq
    omega
  · simpa using hqeq.symm

theorem active_forcedZeroSet_disjoint_mismatchSet
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    Disjoint (forcedZeroSet d g.1 (g.2.card - inputWeight d))
      (mismatchSet d g.2) := by
  apply Finset.disjoint_left.mpr
  intro j hjforced hjmis
  obtain ⟨r, hr0, hrh, rfl, hd⟩ := forcedZeroSet_position hjforced
  have hshape := active_group_shape hdpos hg
  dsimp only at hshape
  have hc := hshape.2.2.2 r hr0 (by omega)
  have hnotmatch : ¬ ((g.1 + (r : ZMod k) ∈ g.2) ↔
      d (g.1 + (r : ZMod k)) = true) := by
    simpa [mismatchSet] using hjmis
  exact hnotmatch ⟨fun _ => hd, fun _ => hc⟩

theorem active_fixed_disjoint
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    Disjoint (fixedOnes d g) (fixedZeros d g) := by
  apply Finset.disjoint_left.mpr
  intro j hjone hjzero
  have hjout : j ∈ outgoingOneSet d g.2 :=
    Finset.mem_of_mem_erase hjone
  have hjmis : j ∈ mismatchSet d g.2 :=
    (Finset.mem_filter.mp hjout).1
  rcases Finset.mem_union.mp hjzero with hjbase | hjforced
  · exact (Finset.mem_sdiff.mp hjbase).2 hjout
  · exact (Finset.disjoint_left.mp
      (active_forcedZeroSet_disjoint_mismatchSet hdpos hg)) hjforced hjmis

theorem active_flip_not_mem_forcedZeroSet
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    g.1 ∉ forcedZeroSet d g.1 (g.2.card - inputWeight d) := by
  intro hi
  obtain ⟨r, hr0, hrh, heq, _⟩ := forcedZeroSet_position hi
  have hshape := active_group_shape hdpos hg
  dsimp only at hshape
  have hrk : r < k := hrh.trans hshape.2.1
  have hcast : (r : ZMod k) ≠ 0 := natCast_ne_zero_of_pos_of_lt hr0 hrk
  apply hcast
  apply add_left_cancel (a := g.1)
  simpa [add_assoc, add_comm, add_left_comm] using heq.symm

theorem active_flip_not_mem_fixedZeros
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    g.1 ∉ fixedZeros d g := by
  intro hi
  rcases Finset.mem_union.mp hi with hbase | hforced
  · exact (Finset.mem_sdiff.mp hbase).2
      (active_flip_mem_outgoingOneSet hdpos hg)
  · exact active_flip_not_mem_forcedZeroSet hdpos hg hforced

def GroupConstraints (d : InputWord k) (g : Group k)
    (s : Finset (ZMod k)) : Prop :=
  g.1 ∉ s ∧ fixedOnes d g ⊆ s ∧ Disjoint (fixedZeros d g) s

theorem pivotal_group_implies_constraints
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d)
    {i : ZMod k} {s : Finset (ZMod k)}
    (hpiv : IsPivotal (propBadFamily d) i s)
    (hgroup : edgeGroup d i s = g) :
    GroupConstraints d g s := by
  classical
  have hiEq : i = g.1 := by
    simpa [edgeGroup] using congrArg Prod.fst hgroup
  subst i
  have hC : carrySet (selectedCarry (inputOfSet (insert g.1 s)) d) = g.2 := by
    simpa [edgeGroup] using congrArg Prod.snd hgroup
  have hc : carryOfSet g.2 = selectedCarry (inputOfSet (insert g.1 s)) d := by
    rw [← hC, carryOfSet_carrySet]
  have hcompat : CarryCompatible (inputOfSet (insert g.1 s)) d
      (carryOfSet g.2) := by
    rw [hc]
    exact selectedCarry_compatible _ _
  have hbits := (compatible_active_group_iff hdpos hg (insert g.1 s)).mp hcompat
  refine ⟨hpiv.1, ?_, ?_⟩
  · intro j hjone
    rcases Finset.mem_erase.mp hjone with ⟨hjne, hjout⟩
    have hjmis := (Finset.mem_filter.mp hjout).1
    have hjnext := (Finset.mem_filter.mp hjout).2
    have hjupper : j ∈ insert g.1 s := (hbits j hjmis).mpr hjnext
    simpa [hjne] using hjupper
  · apply Finset.disjoint_left.mpr
    intro j hjzero hjs
    rcases Finset.mem_union.mp hjzero with hjbase | hjforced
    · have hjmis := (Finset.mem_sdiff.mp hjbase).1
      have hjnext : j + 1 ∉ g.2 := by
        intro hnext
        exact (Finset.mem_sdiff.mp hjbase).2
          (Finset.mem_filter.mpr ⟨hjmis, hnext⟩)
      have hjupper : j ∉ insert g.1 s := by
        intro hmem
        exact hjnext ((hbits j hjmis).mp hmem)
      exact hjupper (Finset.mem_insert_of_mem hjs)
    · obtain ⟨r, hr0, hrh, hjpos, hd⟩ := forcedZeroSet_position hjforced
      have hdata := pivotal_edge_conditions hdpos hpiv
      dsimp only at hdata
      have hcard : weight (selectedCarry (inputOfSet (insert g.1 s)) d) =
          g.2.card := by rw [weight, hC]
      have hrh' : r < weight (selectedCarry (inputOfSet (insert g.1 s)) d) -
          inputWeight d := by simpa [hcard] using hrh
      have hzero := hdata.2.2.2.2.2 r hr0 hrh' (by simpa [hjpos] using hd)
      have hjupper : j ∉ insert g.1 s := by
        have : inputOfSet (insert g.1 s) j = false := by simpa [hjpos] using hzero
        simpa using this
      exact hjupper (Finset.mem_insert_of_mem hjs)

theorem constraints_imply_pivotal_group
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d)
    {s : Finset (ZMod k)} (hs : GroupConstraints d g s) :
    IsPivotal (propBadFamily d) g.1 s ∧ edgeGroup d g.1 s = g := by
  classical
  let upper := inputOfSet (insert g.1 s)
  let c := carryOfSet g.2
  let h := g.2.card - inputWeight d
  have hshape := active_group_shape hdpos hg
  dsimp only at hshape
  have hcompat : CarryCompatible upper d c := by
    apply (compatible_active_group_iff hdpos hg (insert g.1 s)).mpr
    intro j hjmis
    by_cases hjnext : j + 1 ∈ g.2
    · have hjout : j ∈ outgoingOneSet d g.2 :=
        Finset.mem_filter.mpr ⟨hjmis, hjnext⟩
      by_cases hji : j = g.1
      · subst j
        simpa using hjnext
      · have hjone : j ∈ fixedOnes d g :=
          Finset.mem_erase.mpr ⟨hji, hjout⟩
        have hjs : j ∈ s := hs.2.1 hjone
        simp [hji, hjs, hjnext]
    · have hjbase : j ∈ mismatchSet d g.2 \ outgoingOneSet d g.2 := by
        apply Finset.mem_sdiff.mpr
        refine ⟨hjmis, ?_⟩
        intro hjout
        exact hjnext (Finset.mem_filter.mp hjout).2
      have hjzero : j ∈ fixedZeros d g :=
        Finset.mem_union_left _ hjbase
      have hjnotS : j ∉ s := by
        intro hjs
        exact (Finset.disjoint_left.mp hs.2.2) hjzero hjs
      have hji : j ≠ g.1 := by
        intro heq
        subst j
        exact hjnext (Finset.mem_filter.mp
          (active_flip_mem_outgoingOneSet hdpos hg)).2
      simp [hji, hjnotS, hjnext]
  have hcSelected : c = selectedCarry upper d :=
    selectedCarry_eq_active_of_compatible hdpos hg hcompat
  have hweightC : weight c = inputWeight d + h := by
    obtain ⟨_, _, _, _, _, hw, _, _⟩ := active_group_data hdpos hg
    exact hw
  have hcondC : PivotalConditions d upper c g.1 h := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [c, carryOfSet] using hshape.2.2.1
    · intro r hr0 hrh
      simpa [c, carryOfSet] using hshape.2.2.2 r hr0 hrh
    · intro r hr0 hrh hd
      have hjforced : g.1 + (r : ZMod k) ∈ forcedZeroSet d g.1 h :=
        mem_forcedZeroSet_of_position hr0 hrh hd
      have hjzero : g.1 + (r : ZMod k) ∈ fixedZeros d g := by
        exact Finset.mem_union_right _ hjforced
      have hjnotS : g.1 + (r : ZMod k) ∉ s := by
        intro hjS
        exact (Finset.disjoint_left.mp hs.2.2) hjzero hjS
      have hne : g.1 + (r : ZMod k) ≠ g.1 := by
        intro heq
        exact active_flip_not_mem_fixedZeros hdpos hg (heq ▸ hjzero)
      simp [upper, inputOfSet, hne, hjnotS]
  have hweightSelected : weight (selectedCarry upper d) = inputWeight d + h := by
    rw [← hcSelected]
    exact hweightC
  have hlower : weight (selectedCarry (inputOfSet s) d) ≤ inputWeight d := by
    apply rank_below_of_pivotal_conditions
      (inputOfSet_insert_isFlip hs.1) (inputWeight d) h
    · exact hshape.1
    · exact hshape.2.1
    · exact hweightSelected
    · rw [← hcSelected]
      exact hcondC
  have hupperBad : insert g.1 s ∈ propBadFamily d := by
    rw [mem_propBadFamily]
    rw [hweightSelected]
    omega
  have hlowerGood : s ∉ propBadFamily d := by
    rw [mem_propBadFamily]
    omega
  refine ⟨⟨hs.1, hlowerGood, hupperBad⟩, ?_⟩
  apply Prod.ext
  · rfl
  · simp only [edgeGroup]
    change carrySet (selectedCarry upper d) = g.2
    rw [← hcSelected]
    simp [c]

theorem pivotal_group_iff_constraints
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d)
    {i : ZMod k} {s : Finset (ZMod k)} :
    IsPivotal (propBadFamily d) i s ∧ edgeGroup d i s = g ↔
      i = g.1 ∧ GroupConstraints d g s := by
  constructor
  · rintro ⟨hpiv, hgroup⟩
    have hi : i = g.1 := by
      simpa [edgeGroup] using congrArg Prod.fst hgroup
    exact ⟨hi, pivotal_group_implies_constraints hdpos hg hpiv hgroup⟩
  · rintro ⟨rfl, hs⟩
    exact constraints_imply_pivotal_group hdpos hg hs

theorem active_fixedOnes_subset_base
    {d : InputWord k} {g : Group k} :
    fixedOnes d g ⊆ Finset.univ.erase g.1 := by
  intro j hj
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ j⟩

theorem active_fixedZeros_subset_base
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    fixedZeros d g ⊆ Finset.univ.erase g.1 := by
  intro j hj
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_univ j⟩
  intro hji
  subst j
  exact active_flip_not_mem_fixedZeros hdpos hg hj

theorem groupConstraints_iff_subcube
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) (s : Finset (ZMod k)) :
    GroupConstraints d g s ↔
      ∃ u ∈ ((Finset.univ.erase g.1) \
          (fixedOnes d g ∪ fixedZeros d g)).powerset,
        s = fixedOnes d g ∪ u := by
  constructor
  · intro hs
    let u := s \ fixedOnes d g
    refine ⟨u, ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro j hju
      rcases Finset.mem_sdiff.mp hju with ⟨hjs, hjnotOne⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_erase.mpr ⟨fun hji => hs.1 (hji ▸ hjs),
        Finset.mem_univ j⟩, ?_⟩
      intro hjfixed
      rcases Finset.mem_union.mp hjfixed with hjone | hjzero
      · exact hjnotOne hjone
      · exact (Finset.disjoint_left.mp hs.2.2) hjzero hjs
    · ext j
      constructor
      · intro hjs
        by_cases hjone : j ∈ fixedOnes d g
        · exact Finset.mem_union_left _ hjone
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hjs, hjone⟩)
      · intro hj
        rcases Finset.mem_union.mp hj with hjone | hju
        · exact hs.2.1 hjone
        · exact (Finset.mem_sdiff.mp hju).1
  · rintro ⟨u, hu, rfl⟩
    have husub := Finset.mem_powerset.mp hu
    refine ⟨?_, Finset.subset_union_left, ?_⟩
    · intro hi
      rcases Finset.mem_union.mp hi with hione | hiu
      · exact (Finset.mem_erase.mp hione).1 rfl
      · have hibase := (Finset.mem_sdiff.mp (husub hiu)).1
        exact (Finset.mem_erase.mp hibase).1 rfl
    · apply Finset.disjoint_left.mpr
      intro j hjzero hj
      rcases Finset.mem_union.mp hj with hjone | hju
      · exact (Finset.disjoint_left.mp (active_fixed_disjoint hdpos hg))
          hjone hjzero
      · have hjnotFixed := (Finset.mem_sdiff.mp (husub hju)).2
        exact hjnotFixed (Finset.mem_union_right _ hjzero)

theorem active_group_profile
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) (p : ℝ) :
    (∑ i : ZMod k, ∑ s : Finset (ZMod k),
      if IsPivotal (propBadFamily d) i s ∧ edgeGroup d i s = g then
        edgeWeight p i s else 0) =
      p ^ (fixedOnes d g).card * (1 - p) ^ (fixedZeros d g).card := by
  classical
  have hcollapse :
      (∑ i : ZMod k, ∑ s : Finset (ZMod k),
        if IsPivotal (propBadFamily d) i s ∧ edgeGroup d i s = g then
          edgeWeight p i s else 0) =
        ∑ s : Finset (ZMod k),
          if GroupConstraints d g s then edgeWeight p g.1 s else 0 := by
    calc
      _ = ∑ s : Finset (ZMod k),
          if IsPivotal (propBadFamily d) g.1 s ∧ edgeGroup d g.1 s = g then
            edgeWeight p g.1 s else 0 := by
        apply Finset.sum_eq_single g.1
        · intro i _ hne
          apply Finset.sum_eq_zero
          intro s _
          rw [if_neg]
          intro h
          exact hne ((pivotal_group_iff_constraints hdpos hg).mp h).1
        · simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        have heq := pivotal_group_iff_constraints hdpos hg
          (i := g.1) (s := s)
        by_cases hs : GroupConstraints d g s
        · rw [if_pos hs, if_pos (heq.mpr ⟨rfl, hs⟩)]
        · rw [if_neg hs, if_neg]
          intro hpiv
          exact hs (heq.mp hpiv).2
  rw [hcollapse]
  simpa [edgeWeight] using
    (weighted_subcube_sum
      (Finset.univ.erase g.1) (fixedOnes d g) (fixedZeros d g)
      active_fixedOnes_subset_base (active_fixedZeros_subset_base hdpos hg)
      (active_fixed_disjoint hdpos hg) (GroupConstraints d g)
      (groupConstraints_iff_subcube hdpos hg) p)

theorem active_mismatch_balance
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    2 * (outgoingOneSet d g.2).card =
      (mismatchSet d g.2).card + (g.2.card - inputWeight d) := by
  let shift : ZMod k ≃ ZMod k := Equiv.addRight 1
  have hU : ∀ j : ZMod k, j ∈ mismatchSet d g.2 ↔
      ¬ (j ∈ g.2 ↔ j ∈ setOfInput d) := by
    intro j
    simp [mismatchSet, setOfInput]
  have hsupport : ∀ j : ZMod k, j ∉ mismatchSet d g.2 →
      (shift j ∈ g.2 ↔ j ∈ g.2) := by
    intro j hj
    have hmatch : carryOfSet g.2 j ↔ d j = true := by
      by_contra hnot
      apply hj
      simpa [mismatchSet, carryOfSet] using hnot
    have hs := active_group_support hdpos hg j hmatch
    simpa [shift, carryOfSet] using hs
  have hcardD : (setOfInput d).card = inputWeight d := by
    rfl
  have hDC : (setOfInput d).card ≤ g.2.card := by
    have hshape := active_group_shape hdpos hg
    dsimp only at hshape
    rw [hcardD]
    omega
  have hbal := shifted_mismatch_balance shift (mismatchSet d g.2) g.2
    (setOfInput d) hU hsupport hDC
  simpa [shift, outgoingOneSet, hcardD] using hbal

omit [NeZero k] in
theorem forcedZeroSet_card_le
    (d : InputWord k) (i : ZMod k) (h : Nat) :
    (forcedZeroSet d i h).card ≤ h - 1 := by
  calc
    (forcedZeroSet d i h).card ≤
        (((Finset.range (h - 1)).image fun r =>
          i + ((r + 1 : Nat) : ZMod k))).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (Finset.range (h - 1)).card := Finset.card_image_le
    _ = h - 1 := by simp

theorem active_fixedOnes_card
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    (fixedOnes d g).card = (outgoingOneSet d g.2).card - 1 := by
  exact Finset.card_erase_of_mem (active_flip_mem_outgoingOneSet hdpos hg)

theorem active_fixedZeros_card
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    (fixedZeros d g).card =
      (mismatchSet d g.2).card - (outgoingOneSet d g.2).card +
        (forcedZeroSet d g.1 (g.2.card - inputWeight d)).card := by
  have houtSub : outgoingOneSet d g.2 ⊆ mismatchSet d g.2 := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hforcedDisjBase : Disjoint
      (mismatchSet d g.2 \ outgoingOneSet d g.2)
      (forcedZeroSet d g.1 (g.2.card - inputWeight d)) :=
    (active_forcedZeroSet_disjoint_mismatchSet hdpos hg).symm.mono_left
      (Finset.sdiff_subset)
  rw [fixedZeros, Finset.card_union_of_disjoint hforcedDisjBase]
  rw [Finset.card_sdiff_of_subset houtSub]

theorem active_fixedZero_le_fixedOne
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {g : Group k} (hg : g ∈ activeGroups d) :
    (fixedZeros d g).card ≤ (fixedOnes d g).card := by
  have hshape := active_group_shape hdpos hg
  dsimp only at hshape
  have hbal := active_mismatch_balance hdpos hg
  have hforced := forcedZeroSet_card_le d g.1 (g.2.card - inputWeight d)
  have houtSub : outgoingOneSet d g.2 ⊆ mismatchSet d g.2 := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have houtLe := Finset.card_le_card houtSub
  rw [active_fixedZeros_card hdpos hg, active_fixedOnes_card hdpos hg]
  omega

theorem pivotalProfile_eq_activeGroups
    {d : InputWord k} (hdpos : 0 < inputWeight d) (p : ℝ) :
    pivotalProfile (propBadFamily d) p =
      ∑ g ∈ activeGroups d,
        p ^ (fixedOnes d g).card * (1 - p) ^ (fixedZeros d g).card := by
  classical
  calc
    pivotalProfile (propBadFamily d) p =
        ∑ i : ZMod k, ∑ s : Finset (ZMod k), ∑ g ∈ activeGroups d,
          if IsPivotal (propBadFamily d) i s ∧ edgeGroup d i s = g then
            edgeWeight p i s else 0 := by
      unfold pivotalProfile
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro s _
      by_cases hpiv : IsPivotal (propBadFamily d) i s
      · rw [if_pos hpiv]
        have hmem : edgeGroup d i s ∈ activeGroups d :=
          mem_activeGroups_iff.mpr ⟨i, s, hpiv, rfl⟩
        symm
        calc
          _ = if IsPivotal (propBadFamily d) i s ∧
                edgeGroup d i s = edgeGroup d i s then
                edgeWeight p i s else 0 := by
            apply Finset.sum_eq_single (edgeGroup d i s)
            · intro g _ hne
              simp [hne.symm]
            · intro hnot
              exact (hnot hmem).elim
          _ = edgeWeight p i s := by simp [hpiv]
      · simp [hpiv]
    _ = ∑ i : ZMod k, ∑ g ∈ activeGroups d, ∑ s : Finset (ZMod k),
          if IsPivotal (propBadFamily d) i s ∧ edgeGroup d i s = g then
            edgeWeight p i s else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ g ∈ activeGroups d, ∑ i : ZMod k, ∑ s : Finset (ZMod k),
          if IsPivotal (propBadFamily d) i s ∧ edgeGroup d i s = g then
            edgeWeight p i s else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ g ∈ activeGroups d,
        p ^ (fixedOnes d g).card * (1 - p) ^ (fixedZeros d g).card := by
      apply Finset.sum_congr rfl
      intro g hg
      exact active_group_profile hdpos hg p

theorem propBadFamily_profile_comparison
    {d : InputWord k} (hdpos : 0 < inputWeight d)
    {p : ℝ} (hp : p ∈ Set.Icc 0 (1 / 2)) :
    pivotalProfile (propBadFamily d) p ≤
      pivotalProfile (propBadFamily d) (1 - p) := by
  rw [pivotalProfile_eq_activeGroups hdpos,
    pivotalProfile_eq_activeGroups hdpos]
  apply Finset.sum_le_sum
  intro g hg
  have hmono := biasedMonomial_complement_sub_nonneg
    (active_fixedZero_le_fixedOne hdpos hg) hp
  have hle := sub_nonneg.mp hmono
  convert hle using 1; ring

end LeanCipher.TuDengPartition

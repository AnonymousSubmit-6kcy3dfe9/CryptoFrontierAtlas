import Mathlib

open Set
open scoped BigOperators

namespace LeanCipher.TuDengCube

/-!
The finite Boolean-cube calculus used by the pivotal proof of the Tu--Deng
inequality.  A vertex is represented by the finset of coordinates equal to
one.  This avoids any encoding choices for Boolean functions and makes the
lower endpoint of an edge literal: `s` is the lower endpoint in direction
`i` exactly when `i ∉ s`.
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

def IsIncreasing (B : Finset (Finset α)) : Prop :=
  ∀ ⦃s t : Finset α⦄, s ⊆ t → s ∈ B → t ∈ B

def pointWeight (p : ℝ) (s : Finset α) : ℝ :=
  ∏ i : α, if i ∈ s then p else 1 - p

def edgeWeight (p : ℝ) (i : α) (s : Finset α) : ℝ :=
  ∏ j ∈ (Finset.univ.erase i), if j ∈ s then p else 1 - p

/-!
The product measure of a subcube with prescribed one and zero coordinates.
Writing the remaining coordinates as a powerset makes the normalization of
all free coordinates explicit.
-/
omit [Fintype α] in
theorem weighted_powerset_sum
    (base ones zeros : Finset α)
    (hones : ones ⊆ base) (hzeros : zeros ⊆ base)
    (hdisj : Disjoint ones zeros) (p : ℝ) :
    let free := base \ (ones ∪ zeros)
    (∑ t ∈ free.powerset,
      ∏ j ∈ base, if j ∈ ones ∪ t then p else 1 - p) =
      p ^ ones.card * (1 - p) ^ zeros.card := by
  dsimp only
  let free := base \ (ones ∪ zeros)
  have hfreeOnes : Disjoint free ones := by
    rw [Finset.disjoint_left]
    intro j hjfree hjones
    exact (Finset.mem_sdiff.mp hjfree).2 (Finset.mem_union_left zeros hjones)
  have hfreeZeros : Disjoint free zeros := by
    rw [Finset.disjoint_left]
    intro j hjfree hjzeros
    exact (Finset.mem_sdiff.mp hjfree).2 (Finset.mem_union_right ones hjzeros)
  have hcover : ones ∪ zeros ∪ free = base := by
    ext j
    simp only [Finset.mem_union, Finset.mem_sdiff, free]
    constructor
    · rintro (hj | ⟨hjbase, _⟩)
      · exact hj.elim (fun h => hones h) (fun h => hzeros h)
      · exact hjbase
    · intro hjbase
      by_cases hj : j ∈ ones ∨ j ∈ zeros
      · exact Or.inl hj
      · exact Or.inr ⟨hjbase, by simpa using hj⟩
  have hpair : Disjoint (ones ∪ zeros) free := by
    rw [Finset.disjoint_left]
    intro j hjfixed hjfree
    rcases Finset.mem_union.mp hjfixed with hjones | hjzeros
    · exact (Finset.disjoint_left.mp hfreeOnes hjfree) hjones
    · exact (Finset.disjoint_left.mp hfreeZeros hjfree) hjzeros
  have hfixed :
      (∏ j ∈ ones ∪ zeros, if j ∈ ones ∪ (∅ : Finset α) then p else 1 - p) =
        p ^ ones.card * (1 - p) ^ zeros.card := by
    rw [Finset.prod_union hdisj]
    congr 1
    · rw [← Finset.prod_const]
      refine Finset.prod_congr rfl fun j hjones => ?_
      simp [hjones]
    · rw [← Finset.prod_const]
      refine Finset.prod_congr rfl fun j hjzeros => ?_
      have hjnotones : j ∉ ones := fun hjones =>
        (Finset.disjoint_left.mp hdisj hjones) hjzeros
      simp [hjnotones]
  rw [show (∑ t ∈ free.powerset,
      ∏ j ∈ base, if j ∈ ones ∪ t then p else 1 - p) =
      (p ^ ones.card * (1 - p) ^ zeros.card) *
        ∑ t ∈ free.powerset,
          ∏ j ∈ free, if j ∈ t then p else 1 - p by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htfree : t ⊆ free := Finset.mem_powerset.mp ht
    have hsplit :
        (∏ j ∈ base, if j ∈ ones ∪ t then p else 1 - p) =
          (∏ j ∈ ones ∪ zeros, if j ∈ ones ∪ t then p else 1 - p) *
            ∏ j ∈ free, if j ∈ ones ∪ t then p else 1 - p := by
      calc
        _ = ∏ j ∈ (ones ∪ zeros) ∪ free,
            if j ∈ ones ∪ t then p else 1 - p := by rw [hcover]
        _ = _ := Finset.prod_union hpair
    rw [hsplit]
    congr 1
    · rw [← hfixed]
      apply Finset.prod_congr rfl
      intro j hj
      have hjnotfree : j ∉ free := Finset.disjoint_left.mp hpair hj
      have hjnott : j ∉ t := fun hjt => hjnotfree (htfree hjt)
      simp [hjnott]
    · apply Finset.prod_congr rfl
      intro j hj
      have hjnotones : j ∉ ones := Finset.disjoint_left.mp hfreeOnes hj
      simp [hjnotones]]
  have hfreeSum :
      (∑ t ∈ free.powerset,
        ∏ j ∈ free, if j ∈ t then p else 1 - p) = 1 := by
    rw [show (∑ t ∈ free.powerset,
        ∏ j ∈ free, if j ∈ t then p else 1 - p) =
        ∑ t ∈ free.powerset,
          (∏ j ∈ t, p) * ∏ j ∈ free \ t, (1 - p) by
      refine Finset.sum_congr rfl fun t ht => ?_
      have htfree : t ⊆ free := Finset.mem_powerset.mp ht
      rw [Finset.prod_ite]
      congr 2
      · ext j
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun hjt => ⟨htfree hjt, hjt⟩
      · ext j
        simp]
    have hadd := Finset.prod_add (fun _ : α => p) (fun _ => 1 - p) free
    rw [show (∑ t ∈ free.powerset,
        (∏ j ∈ t, p) * ∏ j ∈ free \ t, (1 - p)) =
        ∏ j ∈ free, (p + (1 - p)) by exact hadd.symm]
    simp
  rw [hfreeSum]
  simp

omit [Fintype α] in
theorem subcube_constraints_iff
    (base ones zeros s : Finset α)
    (hones : ones ⊆ base) (hdisj : Disjoint ones zeros) :
    s ⊆ base ∧ ones ⊆ s ∧ Disjoint zeros s ↔
      ∃ t ∈ (base \ (ones ∪ zeros)).powerset, s = ones ∪ t := by
  constructor
  · rintro ⟨hsbase, honesS, hzeroS⟩
    refine ⟨s \ ones, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_sdiff.mp hj with ⟨hjs, hjones⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hsbase hjs, ?_⟩
      intro hjunion
      rcases Finset.mem_union.mp hjunion with hjon | hjzero
      · exact hjones hjon
      · exact (Finset.disjoint_left.mp hzeroS hjzero) hjs
    · exact (Finset.union_sdiff_of_subset honesS).symm
  · rintro ⟨t, ht, rfl⟩
    have htfree : t ⊆ base \ (ones ∪ zeros) :=
      Finset.mem_powerset.mp ht
    refine ⟨?_, Finset.subset_union_left, ?_⟩
    · intro j hj
      rcases Finset.mem_union.mp hj with hjone | hjt
      · exact hones hjone
      · exact (Finset.mem_sdiff.mp (htfree hjt)).1
    · rw [Finset.disjoint_left]
      intro j hjzero hjunion
      rcases Finset.mem_union.mp hjunion with hjone | hjt
      · exact (Finset.disjoint_left.mp hdisj hjone) hjzero
      · exact (Finset.mem_sdiff.mp (htfree hjt)).2
          (Finset.mem_union_right ones hjzero)

theorem weighted_subcube_sum
    (base ones zeros : Finset α)
    (hones : ones ⊆ base) (hzeros : zeros ⊆ base)
    (hdisj : Disjoint ones zeros)
    (Q : Finset α → Prop) [DecidablePred Q]
    (hQ : ∀ s,
      Q s ↔
        ∃ t ∈ (base \ (ones ∪ zeros)).powerset, s = ones ∪ t)
    (p : ℝ) :
    (∑ s : Finset α,
      if Q s then
        ∏ j ∈ base, if j ∈ s then p else 1 - p
      else 0) =
      p ^ ones.card * (1 - p) ^ zeros.card := by
  let free := base \ (ones ∪ zeros)
  have hfreeOnes : Disjoint free ones := by
    rw [Finset.disjoint_left]
    intro j hjfree hjones
    exact (Finset.mem_sdiff.mp hjfree).2 (Finset.mem_union_left zeros hjones)
  rw [← Finset.sum_filter]
  calc
    (∑ s ∈ (Finset.univ : Finset (Finset α)) with Q s,
        ∏ j ∈ base, if j ∈ s then p else 1 - p) =
        ∑ t ∈ free.powerset,
          ∏ j ∈ base, if j ∈ ones ∪ t then p else 1 - p := by
      apply Finset.sum_bij'
        (fun s _ => s \ ones)
        (fun t _ => ones ∪ t)
      · intro s hs
        have hsQ : Q s := (Finset.mem_filter.mp hs).2
        obtain ⟨t, ht, hst⟩ := (hQ s).mp hsQ
        have htfree : t ⊆ free := by
          simpa [free] using Finset.mem_powerset.mp ht
        have hton : Disjoint t ones := hfreeOnes.mono_left htfree
        have htdiff : t \ ones = t := by
          ext j
          simp only [Finset.mem_sdiff]
          constructor
          · exact fun hj => hj.1
          · exact fun hj => ⟨hj, fun hjone =>
              (Finset.disjoint_left.mp hton hj) hjone⟩
        apply Finset.mem_powerset.mpr
        rw [hst, Finset.union_sdiff_left]
        simpa [htdiff] using htfree
      · intro t ht
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, (hQ (ones ∪ t)).mpr ?_⟩
        exact ⟨t, by simpa [free] using ht, rfl⟩
      · intro s hs
        have hsQ : Q s := (Finset.mem_filter.mp hs).2
        obtain ⟨t, ht, hst⟩ := (hQ s).mp hsQ
        have htfree : t ⊆ free := by
          simpa [free] using Finset.mem_powerset.mp ht
        have hton : Disjoint t ones := hfreeOnes.mono_left htfree
        have htdiff : t \ ones = t := by
          ext j
          simp only [Finset.mem_sdiff]
          constructor
          · exact fun hj => hj.1
          · exact fun hj => ⟨hj, fun hjone =>
              (Finset.disjoint_left.mp hton hj) hjone⟩
        rw [hst, Finset.union_sdiff_left]
        rw [htdiff]
      · intro t ht
        have htfree : t ⊆ free := by
          simpa [free] using Finset.mem_powerset.mp ht
        have hton : Disjoint t ones := hfreeOnes.mono_left htfree
        have htdiff : t \ ones = t := by
          ext j
          simp only [Finset.mem_sdiff]
          constructor
          · exact fun hj => hj.1
          · exact fun hj => ⟨hj, fun hjone =>
              (Finset.disjoint_left.mp hton hj) hjone⟩
        rw [Finset.union_sdiff_left]
        exact htdiff
      · intro s hs
        have hsQ : Q s := (Finset.mem_filter.mp hs).2
        obtain ⟨t, ht, hst⟩ := (hQ s).mp hsQ
        have htfree : t ⊆ free := by
          simpa [free] using Finset.mem_powerset.mp ht
        have hton : Disjoint t ones := hfreeOnes.mono_left htfree
        have htdiff : t \ ones = t := by
          ext j
          simp only [Finset.mem_sdiff]
          constructor
          · exact fun hj => hj.1
          · exact fun hj => ⟨hj, fun hjone =>
              (Finset.disjoint_left.mp hton hj) hjone⟩
        rw [hst, Finset.union_sdiff_left, htdiff]
    _ = p ^ ones.card * (1 - p) ^ zeros.card := by
      exact weighted_powerset_sum base ones zeros hones hzeros hdisj p

/-!
A finite-set form of the cyclic telescoping identity in P8.  The equivalence
`shift` is the cyclic successor, `C` is the carry-one set, `D` the target-one
set, and `U` their mismatch set.  Outside `U`, support makes carry membership
invariant under `shift`; bijectivity then balances incoming and outgoing ones.
-/
theorem shifted_mismatch_balance
    (shift : α ≃ α) (U C D : Finset α)
    (hU : ∀ j, j ∈ U ↔ ¬ (j ∈ C ↔ j ∈ D))
    (hsupport : ∀ j, j ∉ U → (shift j ∈ C ↔ j ∈ C))
    (hDC : D.card ≤ C.card) :
    let R := U.filter fun j => shift j ∈ C
    2 * R.card = U.card + (C.card - D.card) := by
  dsimp only
  let preC := (Finset.univ : Finset α).filter fun j => shift j ∈ C
  let inC := (Finset.univ : Finset α).filter fun j => j ∈ C
  let Rout := preC.filter fun j => j ∈ U
  let Rcomp := preC.filter fun j => j ∉ U
  let Ain := inC.filter fun j => j ∈ U
  let Acomp := inC.filter fun j => j ∉ U
  have hpreCard : preC.card = C.card := by
    apply Finset.card_bij (fun j _ => shift j)
    · intro j hj
      simp only [preC, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    · intro a ha b hb hab
      exact shift.injective hab
    · intro c hc
      refine ⟨shift.symm c, ?_, shift.apply_symm_apply c⟩
      simp only [preC, Finset.mem_filter, Finset.mem_univ, true_and,
        shift.apply_symm_apply]
      exact hc
  have hinCard : inC.card = C.card := by
    simp [inC]
  have hRout : Rout = U.filter fun j => shift j ∈ C := by
    ext j
    simp [Rout, preC, and_comm]
  have hAin : Ain = U.filter fun j => j ∈ C := by
    ext j
    simp [Ain, inC, and_comm]
  have hcomp : Rcomp = Acomp := by
    ext j
    simp only [Rcomp, Acomp, preC, inC, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hjC, hjU⟩
      exact ⟨(hsupport j hjU).mp hjC, hjU⟩
    · rintro ⟨hjC, hjU⟩
      exact ⟨(hsupport j hjU).mpr hjC, hjU⟩
  have hpreSplit : Rout.card + Rcomp.card = preC.card := by
    simpa [Rout, Rcomp] using
      (Finset.card_filter_add_card_filter_not (s := preC) fun j => j ∈ U)
  have hinSplit : Ain.card + Acomp.card = inC.card := by
    simpa [Ain, Acomp] using
      (Finset.card_filter_add_card_filter_not (s := inC) fun j => j ∈ U)
  have hRA : (U.filter fun j => shift j ∈ C).card =
      (U.filter fun j => j ∈ C).card := by
    rw [← hRout, ← hAin]
    rw [hpreCard] at hpreSplit
    rw [hinCard] at hinSplit
    rw [hcomp] at hpreSplit
    omega
  let A := C \ D
  let B := D \ C
  have hAset : U.filter (fun j => j ∈ C) = A := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_sdiff, A]
    constructor
    · rintro ⟨hjU, hjC⟩
      have hne := (hU j).mp hjU
      exact ⟨hjC, fun hjD => hne ⟨fun _ => hjD, fun _ => hjC⟩⟩
    · rintro ⟨hjC, hjD⟩
      exact ⟨(hU j).mpr (fun heq => hjD (heq.mp hjC)), hjC⟩
  have hUset : U = A ∪ B := by
    ext j
    simp only [Finset.mem_union, Finset.mem_sdiff, A, B]
    rw [hU j]
    tauto
  have hABdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    exact (Finset.mem_sdiff.mp hjA).2 (Finset.mem_sdiff.mp hjB).1
  have hUcard : U.card = A.card + B.card := by
    rw [hUset, Finset.card_union_of_disjoint hABdisj]
  have hCD : C.card + B.card = D.card + A.card := by
    have hc := Finset.card_sdiff_add_card_inter C D
    have hd := Finset.card_sdiff_add_card_inter D C
    have hinter : (C ∩ D).card = (D ∩ C).card := by
      congr 1
      exact Finset.inter_comm C D
    dsimp [A, B]
    omega
  rw [hRA, hAset, hUcard]
  omega

def biasedMass (B : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ s ∈ B, pointWeight p s

@[reducible] def IsPivotal (B : Finset (Finset α)) (i : α) (s : Finset α) : Prop :=
  i ∉ s ∧ s ∉ B ∧ insert i s ∈ B

def pivotalProfile (B : Finset (Finset α)) (p : ℝ) : ℝ :=
  ∑ i : α, ∑ s : Finset α,
    if IsPivotal B i s then edgeWeight p i s else 0

omit [Fintype α] in
private theorem hasDerivAt_factor (s : Finset α) (i : α) (p : ℝ) :
    HasDerivAt (fun q : ℝ => if i ∈ s then q else 1 - q)
      (if i ∈ s then 1 else -1) p := by
  by_cases hi : i ∈ s
  · simpa [hi] using hasDerivAt_id p
  · simpa [hi] using
      (hasDerivAt_const (x := p) (c := (1 : ℝ))).sub (hasDerivAt_id p)

theorem hasDerivAt_pointWeight (s : Finset α) (p : ℝ) :
    HasDerivAt (pointWeight (α := α) · s)
      (∑ i : α, (if i ∈ s then (1 : ℝ) else -1) * edgeWeight p i s) p := by
  have h := HasDerivAt.finset_prod
    (u := (Finset.univ : Finset α))
    (f := fun (i : α) (q : ℝ) => if i ∈ s then q else 1 - q)
    (f' := fun i => if i ∈ s then (1 : ℝ) else -1)
    (x := p) (fun i _ => hasDerivAt_factor s i p)
  simpa [pointWeight, edgeWeight, smul_eq_mul, Finset.prod_fn] using h

private theorem edgeWeight_insert_self (p : ℝ) (i : α) (s : Finset α) :
    edgeWeight p i (insert i s) = edgeWeight p i s := by
  unfold edgeWeight
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hji]

private theorem sum_pair_by_coordinate (i : α) (f : Finset α → ℝ) :
    ∑ s : Finset α, f s =
      ∑ s ∈ (Finset.univ.filter fun s : Finset α => i ∉ s),
        (f s + f (insert i s)) := by
  classical
  let without := Finset.univ.filter fun s : Finset α => i ∉ s
  let containing := Finset.univ.filter fun s : Finset α => i ∈ s
  have hpair : (∑ s ∈ containing, f s) = ∑ s ∈ without, f (insert i s) := by
    apply Finset.sum_bij (fun s _ => s.erase i)
    · intro s hs
      simp only [containing, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp [without]
    · intro s hs t ht hst
      simp only [containing, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
      rw [← Finset.insert_erase hs, ← Finset.insert_erase ht, hst]
    · intro t ht
      simp only [without, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      refine ⟨insert i t, ?_, ?_⟩
      · simp [containing]
      · simp [ht]
    · intro s hs
      simp only [containing, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [Finset.insert_erase hs]
  calc
    ∑ s : Finset α, f s = (∑ s ∈ containing, f s) + ∑ s ∈ without, f s := by
      simpa only [containing, without] using
        (Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (Finset α)) (fun s => i ∈ s) f).symm
    _ = (∑ s ∈ without, f (insert i s)) + ∑ s ∈ without, f s := by rw [hpair]
    _ = ∑ s ∈ without, (f s + f (insert i s)) := by
      rw [Finset.sum_add_distrib]
      exact add_comm _ _

private theorem coordinate_derivative_eq_pivotal
    (B : Finset (Finset α))
    (hB : IsIncreasing B) (i : α) (p : ℝ) :
    (∑ s : Finset α,
        if s ∈ B then
          (if i ∈ s then (1 : ℝ) else -1) * edgeWeight p i s
        else 0) =
      ∑ s : Finset α,
        if IsPivotal B i s then edgeWeight p i s else 0 := by
  rw [sum_pair_by_coordinate i, sum_pair_by_coordinate i]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  by_cases hslow : s ∈ B
  · have hsupper : insert i s ∈ B := hB (Finset.subset_insert i s) hslow
    simp [IsPivotal, hs, hslow, hsupper, edgeWeight_insert_self]
  · by_cases hsupper : insert i s ∈ B
    · simp [IsPivotal, hs, hslow, hsupper, edgeWeight_insert_self]
    · simp [IsPivotal, hs, hslow, hsupper]

theorem hasDerivAt_biasedMass_eq_pivotalProfile
    (B : Finset (Finset α))
    (hB : IsIncreasing B) (p : ℝ) :
    HasDerivAt (biasedMass B) (pivotalProfile B p) p := by
  have hmass :
      HasDerivAt (biasedMass B)
        (∑ s ∈ B, ∑ i : α,
          (if i ∈ s then (1 : ℝ) else -1) * edgeWeight p i s) p := by
    simpa [biasedMass, Finset.sum_fn] using
      (HasDerivAt.sum (u := B) fun s _ => hasDerivAt_pointWeight s p)
  have hprofile :
      (∑ s ∈ B, ∑ i : α,
          (if i ∈ s then (1 : ℝ) else -1) * edgeWeight p i s) =
        pivotalProfile B p := by
    unfold pivotalProfile
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa using coordinate_derivative_eq_pivotal B hB i p
  rw [← hprofile]
  exact hmass

/-!
`PivotalSubcubePartition` is the interface between a problem-specific edge
classification and the generic analytic argument.  `groupOf` makes the
groups disjoint and exhaustive.  The `group_profile` field is the precise
subcube obligation: after summing the free coordinates, the group must have
the monomial determined by its fixed-one and fixed-zero sets.
-/

structure PivotalSubcubePartition (B : Finset (Finset α)) (ι : Type*)
    [Fintype ι] [DecidableEq ι] where
  groupOf : α → Finset α → ι
  fixedOnes : ι → Finset α
  fixedZeros : ι → Finset α
  fixed_disjoint : ∀ g, Disjoint (fixedOnes g) (fixedZeros g)
  group_profile : ∀ (g : ι) (p : ℝ),
    (∑ i : α, ∑ s : Finset α,
      if IsPivotal B i s ∧ groupOf i s = g then edgeWeight p i s else 0) =
      p ^ (fixedOnes g).card * (1 - p) ^ (fixedZeros g).card
  fixedZero_le_fixedOne : ∀ g, (fixedZeros g).card ≤ (fixedOnes g).card

theorem pivotalProfile_eq_sum_groupProfiles
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Finset (Finset α)) (P : PivotalSubcubePartition B ι) (p : ℝ) :
    pivotalProfile B p =
      ∑ g : ι, p ^ (P.fixedOnes g).card * (1 - p) ^ (P.fixedZeros g).card := by
  classical
  calc
    pivotalProfile B p =
        ∑ i : α, ∑ s : Finset α, ∑ g : ι,
          if IsPivotal B i s ∧ P.groupOf i s = g then edgeWeight p i s else 0 := by
      unfold pivotalProfile
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro s _
      by_cases hpiv : IsPivotal B i s
      · rw [if_pos hpiv]
        calc
          edgeWeight p i s = ∑ g : ι,
              if P.groupOf i s = g then edgeWeight p i s else 0 := by
            rw [Finset.sum_ite_eq]
            simp
          _ = ∑ g : ι,
              if IsPivotal B i s ∧ P.groupOf i s = g then edgeWeight p i s else 0 := by
            apply Finset.sum_congr rfl
            intro g _
            by_cases hg : P.groupOf i s = g
            · rw [if_pos hg, if_pos ⟨hpiv, hg⟩]
            · rw [if_neg hg, if_neg (fun h => hg h.2)]
      · simp [hpiv]
    _ = ∑ i : α, ∑ g : ι, ∑ s : Finset α,
          if IsPivotal B i s ∧ P.groupOf i s = g then edgeWeight p i s else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ g : ι, ∑ i : α, ∑ s : Finset α,
          if IsPivotal B i s ∧ P.groupOf i s = g then edgeWeight p i s else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ g : ι,
          p ^ (P.fixedOnes g).card * (1 - p) ^ (P.fixedZeros g).card := by
      apply Finset.sum_congr rfl
      intro g _
      exact P.group_profile g p

theorem biasedMonomial_complement_sub_nonneg
    {a b : Nat} (hab : b ≤ a) {p : ℝ} (hp : p ∈ Set.Icc 0 (1 / 2)) :
    0 ≤ (1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b := by
  have hp0 : 0 ≤ p := hp.1
  have hcomp : p ≤ 1 - p := by linarith [hp.2]
  have h1p : 0 ≤ 1 - p := by linarith [hp.2]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  have hpow : p ^ d ≤ (1 - p) ^ d := pow_le_pow_left₀ hp0 hcomp d
  have hcommon : 0 ≤ (1 - p) ^ b * p ^ b :=
    mul_nonneg (pow_nonneg h1p b) (pow_nonneg hp0 b)
  have hmul :
      (1 - p) ^ b * p ^ b * p ^ d ≤
        (1 - p) ^ b * p ^ b * (1 - p) ^ d :=
    mul_le_mul_of_nonneg_left hpow hcommon
  have hleft :
      p ^ a * (1 - p) ^ b = (1 - p) ^ b * p ^ b * p ^ d := by
    rw [hd, pow_add]
    ring
  have hright :
      (1 - p) ^ b * p ^ b * (1 - p) ^ d = (1 - p) ^ a * p ^ b := by
    rw [hd, pow_add]
    ring
  rw [sub_nonneg, hleft, ← hright]
  exact hmul

theorem pivotalProfile_complement_sub_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Finset (Finset α)) (P : PivotalSubcubePartition B ι)
    {p : ℝ} (hp : p ∈ Set.Icc 0 (1 / 2)) :
    0 ≤ pivotalProfile B (1 - p) - pivotalProfile B p := by
  rw [pivotalProfile_eq_sum_groupProfiles B P,
    pivotalProfile_eq_sum_groupProfiles B P, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro g _
  have hg := biasedMonomial_complement_sub_nonneg (P.fixedZero_le_fixedOne g) hp
  convert hg using 1
  all_goals ring

theorem pointWeight_zero (s : Finset α) :
    pointWeight (α := α) 0 s = if s = ∅ then 1 else 0 := by
  by_cases hs : s = ∅
  · subst s
    simp [pointWeight]
  · rw [if_neg hs]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    unfold pointWeight
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem pointWeight_one (s : Finset α) :
    pointWeight (α := α) 1 s = if s = Finset.univ then 1 else 0 := by
  by_cases hs : s = Finset.univ
  · subst s
    simp [pointWeight]
  · rw [if_neg hs]
    have hex : ∃ i : α, i ∉ s := by
      by_contra h
      apply hs
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    unfold pointWeight
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem pointWeight_half (s : Finset α) :
    pointWeight (α := α) (1 / 2) s =
      (1 / 2 : ℝ) ^ Fintype.card α := by
  unfold pointWeight
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [hhalf, ite_self, Finset.prod_const, Finset.card_univ]

theorem biasedMass_zero (B : Finset (Finset α)) (hzero : ∅ ∉ B) :
    biasedMass B 0 = 0 := by
  simp [biasedMass, pointWeight_zero, hzero]

theorem biasedMass_one (B : Finset (Finset α)) (hone : Finset.univ ∈ B) :
    biasedMass B 1 = 1 := by
  simp [biasedMass, pointWeight_one, hone]

theorem biasedMass_half (B : Finset (Finset α)) :
    biasedMass B (1 / 2) =
      (B.card : ℝ) * (1 / 2 : ℝ) ^ Fintype.card α := by
  unfold biasedMass
  calc
    (∑ s ∈ B, pointWeight (1 / 2) s) =
        ∑ _s ∈ B, (1 / 2 : ℝ) ^ Fintype.card α := by
      apply Finset.sum_congr rfl
      intro s _
      exact pointWeight_half s
    _ = (B.card : ℝ) * (1 / 2 : ℝ) ^ Fintype.card α := by simp

/-!
The Tu--Deng-specific combinatorics naturally sums only over pivotal groups
which actually occur.  This direct interface keeps that finite support in the
problem-specific layer: P11 needs only the resulting comparison of the two
pivotal profiles, not a globally inhabited type of nonempty groups.
-/
theorem biasedMass_half_le_half_of_profile_comparison
    (B : Finset (Finset α)) (hB : IsIncreasing B)
    (hzero : ∅ ∉ B) (hone : Finset.univ ∈ B)
    (hprofile : ∀ {p : ℝ}, p ∈ Set.Icc 0 (1 / 2) →
      pivotalProfile B p ≤ pivotalProfile B (1 - p)) :
    biasedMass B (1 / 2) ≤ 1 / 2 := by
  let H : ℝ → ℝ := fun p => biasedMass B (1 - p) + biasedMass B p
  have hH (p : ℝ) :
      HasDerivAt H (-pivotalProfile B (1 - p) + pivotalProfile B p) p := by
    have hleft :=
      (hasDerivAt_biasedMass_eq_pivotalProfile B hB (1 - p)).comp p
        ((hasDerivAt_const (x := p) (c := (1 : ℝ))).sub (hasDerivAt_id p))
    have hright := hasDerivAt_biasedMass_eq_pivotalProfile B hB p
    dsimp only [H]
    convert hleft.add hright using 1; ring
  have hHcont : Continuous H :=
    continuous_iff_continuousAt.mpr fun p => (hH p).continuousAt
  have hanti : AntitoneOn H (Set.Icc 0 (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / 2))
      hHcont.continuousOn
    · intro p _
      exact (hH p).hasDerivWithinAt
    · intro p hp
      have hp' : p ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset hp
      have hprofile' := hprofile hp'
      linarith
  have hHle := hanti (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num) (by norm_num)
  dsimp only [H] at hHle
  norm_num at hHle
  rw [biasedMass_zero B hzero, biasedMass_one B hone] at hHle
  norm_num at hHle ⊢
  linarith

theorem card_le_half_cube_of_profile_comparison
    (B : Finset (Finset α)) (hB : IsIncreasing B)
    (hzero : ∅ ∉ B) (hone : Finset.univ ∈ B)
    (hprofile : ∀ {p : ℝ}, p ∈ Set.Icc 0 (1 / 2) →
      pivotalProfile B p ≤ pivotalProfile B (1 - p)) :
    B.card ≤ 2 ^ (Fintype.card α - 1) := by
  have hmass := biasedMass_half_le_half_of_profile_comparison
    B hB hzero hone hprofile
  rw [biasedMass_half] at hmass
  have hpowpos : 0 < (2 : ℝ) ^ Fintype.card α := pow_pos (by norm_num) _
  have hdiv :
      (B.card : ℝ) / (2 : ℝ) ^ Fintype.card α ≤ 1 / 2 := by
    convert hmass using 1
    rw [div_eq_mul_inv, div_pow]
    norm_num
  have hcard :
      (B.card : ℝ) ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ Fintype.card α :=
    (div_le_iff₀ hpowpos).mp hdiv
  have hreal : (2 : ℝ) * B.card ≤ (2 : ℝ) ^ Fintype.card α := by
    linarith
  have htwice : 2 * B.card ≤ 2 ^ Fintype.card α := by
    exact_mod_cast hreal
  have hn0 : Fintype.card α ≠ 0 := by
    intro hn
    have huniv : (Finset.univ : Finset α) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using hn
    rw [huniv] at hone
    exact hzero hone
  have hpow : 2 ^ Fintype.card α = 2 * 2 ^ (Fintype.card α - 1) := by
    obtain ⟨n, hncard⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hncard]
    simp [pow_succ, Nat.mul_comm]
  rw [hpow] at htwice
  omega

theorem biasedMass_half_le_half_of_subcube_partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Finset (Finset α)) (hB : IsIncreasing B)
    (hzero : ∅ ∉ B) (hone : Finset.univ ∈ B)
    (P : PivotalSubcubePartition B ι) :
    biasedMass B (1 / 2) ≤ 1 / 2 := by
  let H : ℝ → ℝ := fun p => biasedMass B (1 - p) + biasedMass B p
  have hH (p : ℝ) :
      HasDerivAt H (-pivotalProfile B (1 - p) + pivotalProfile B p) p := by
    have hleft :=
      (hasDerivAt_biasedMass_eq_pivotalProfile B hB (1 - p)).comp p
        ((hasDerivAt_const (x := p) (c := (1 : ℝ))).sub (hasDerivAt_id p))
    have hright := hasDerivAt_biasedMass_eq_pivotalProfile B hB p
    dsimp only [H]
    convert hleft.add hright using 1
    all_goals ring
  have hHcont : Continuous H :=
    continuous_iff_continuousAt.mpr fun p => (hH p).continuousAt
  have hanti : AntitoneOn H (Set.Icc 0 (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / 2))
      hHcont.continuousOn
    · intro p _
      exact (hH p).hasDerivWithinAt
    · intro p hp
      have hp' : p ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset hp
      have hprofile := pivotalProfile_complement_sub_nonneg B P hp'
      linarith
  have hHle := hanti (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num) (by norm_num)
  dsimp only [H] at hHle
  norm_num at hHle
  rw [biasedMass_zero B hzero, biasedMass_one B hone] at hHle
  norm_num at hHle ⊢
  linarith

theorem twice_card_le_cube_card_of_subcube_partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Finset (Finset α)) (hB : IsIncreasing B)
    (hzero : ∅ ∉ B) (hone : Finset.univ ∈ B)
    (P : PivotalSubcubePartition B ι) :
    2 * B.card ≤ 2 ^ Fintype.card α := by
  have hmass := biasedMass_half_le_half_of_subcube_partition B hB hzero hone P
  rw [biasedMass_half] at hmass
  have hpowpos : 0 < (2 : ℝ) ^ Fintype.card α := pow_pos (by norm_num) _
  have hdiv :
      (B.card : ℝ) / (2 : ℝ) ^ Fintype.card α ≤ 1 / 2 := by
    convert hmass using 1
    rw [div_eq_mul_inv, div_pow]
    norm_num
  have hcard :
      (B.card : ℝ) ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ Fintype.card α :=
    (div_le_iff₀ hpowpos).mp hdiv
  have hreal : (2 : ℝ) * B.card ≤ (2 : ℝ) ^ Fintype.card α := by
    linarith
  exact_mod_cast hreal

theorem card_le_half_cube_of_subcube_partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Finset (Finset α)) (hB : IsIncreasing B)
    (hzero : ∅ ∉ B) (hone : Finset.univ ∈ B)
    (P : PivotalSubcubePartition B ι) :
    B.card ≤ 2 ^ (Fintype.card α - 1) := by
  have hn0 : Fintype.card α ≠ 0 := by
    intro hn
    have huniv : (Finset.univ : Finset α) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using hn
    rw [huniv] at hone
    exact hzero hone
  have hn : 1 ≤ Fintype.card α := Nat.one_le_iff_ne_zero.mpr hn0
  have htwice := twice_card_le_cube_card_of_subcube_partition B hB hzero hone P
  have hpow : 2 ^ Fintype.card α = 2 * 2 ^ (Fintype.card α - 1) := by
    obtain ⟨n, hncard⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hncard]
    simp [pow_succ, Nat.mul_comm]
  rw [hpow] at htwice
  omega

end LeanCipher.TuDengCube

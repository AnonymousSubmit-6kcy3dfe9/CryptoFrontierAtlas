import Mathlib.Order.FixedPoints
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

namespace LeanCipher.TuDengCyclic

variable {k : Nat} [NeZero k]

abbrev InputWord (k : Nat) := ZMod k -> Bool
abbrev CarryWord (k : Nat) := ZMod k -> Prop

def gate (state : Prop) (input target : Bool) : Prop :=
  if input = target then target = true else state

theorem gate_mono_state {a b : Prop} {x d : Bool} (h : a -> b) :
    gate a x d -> gate b x d := by
  unfold gate
  split <;> simp_all

theorem gate_mono_input {state : Prop} {x y d : Bool} (h : x.toNat <= y.toNat) :
    gate state x d -> gate state y d := by
  cases x <;> cases y <;> cases d <;> simp_all [gate]

def carryOperator (x d : InputWord k) : CarryWord k →o CarryWord k where
  toFun c j := gate (c (j - 1)) (x (j - 1)) (d (j - 1))
  monotone' := by
    intro c c' h j
    exact gate_mono_state (h (j - 1))

def selectedCarry (x d : InputWord k) : CarryWord k :=
  (carryOperator x d).gfp

def CarryCompatible (x d : InputWord k) (c : CarryWord k) : Prop :=
  forall j, c (j + 1) <-> gate (c j) (x j) (d j)

omit [NeZero k] in
theorem selectedCarry_fixed (x d : InputWord k) :
    carryOperator x d (selectedCarry x d) = selectedCarry x d :=
  (carryOperator x d).map_gfp

omit [NeZero k] in
theorem selectedCarry_compatible (x d : InputWord k) :
    CarryCompatible x d (selectedCarry x d) := by
  intro j
  have h := congrFun (selectedCarry_fixed x d) (j + 1)
  simpa [carryOperator] using iff_of_eq h.symm

omit [NeZero k] in
theorem compatible_le_selected {x d : InputWord k} {c : CarryWord k}
    (hc : CarryCompatible x d c) : c <= selectedCarry x d := by
  apply (carryOperator x d).le_gfp
  intro j hj
  have h := (hc (j - 1)).mp (by simpa using hj)
  simpa [carryOperator] using h

omit [NeZero k] in
theorem selectedCarry_mono {x y d : InputWord k}
    (hxy : forall j, (x j).toNat <= (y j).toNat) :
    selectedCarry x d <= selectedCarry y d := by
  change (carryOperator x d).gfp <= (carryOperator y d).gfp
  apply OrderHom.gfp.monotone
  show carryOperator x d <= carryOperator y d
  intro c j
  exact gate_mono_input (hxy (j - 1))

omit [NeZero k] in
theorem compatible_support {x d : InputWord k} {c : CarryWord k}
    (hc : CarryCompatible x d c) {j : ZMod k} (hmatch : c j <-> d j = true) :
    c (j + 1) <-> c j := by
  rw [hc j]
  unfold gate
  by_cases hxd : x j = d j
  · rw [if_pos hxd, hmatch]
  · rw [if_neg hxd]

omit [NeZero k] in
theorem compatible_mismatch {x d : InputWord k} {c : CarryWord k}
    (hc : CarryCompatible x d c) {j : ZMod k} (hmis : ¬ (c j <-> d j = true)) :
    (x j = true) <-> c (j + 1) := by
  rw [hc j]
  cases hx : x j <;> cases hd : d j <;>
    simp [gate, hd] at hmis ⊢ <;> assumption

noncomputable def carrySet (c : CarryWord k) : Finset (ZMod k) :=
  by classical exact Finset.univ.filter c

noncomputable def weight (c : CarryWord k) : Nat := (carrySet c).card

noncomputable def diffSet (upper lower : CarryWord k) : Finset (ZMod k) :=
  carrySet upper \ carrySet lower

theorem carrySet_mono {upper lower : CarryWord k} (h : lower <= upper) :
    carrySet lower ⊆ carrySet upper := by
  classical
  intro i hi
  simp [carrySet] at hi ⊢
  exact h i hi

theorem weight_eq_add_diff_card {upper lower : CarryWord k} (h : lower <= upper) :
    weight upper = weight lower + (diffSet upper lower).card := by
  classical
  have hsub := carrySet_mono h
  unfold weight diffSet
  have hd := Finset.card_sdiff_add_card_eq_card hsub
  omega

def cycleEquiv (i : ZMod k) : Fin k ≃ ZMod k :=
  (ZMod.finEquiv k).toEquiv.trans (Equiv.addRight i)

@[simp] theorem cycleEquiv_apply (i : ZMod k) (r : Fin k) :
    cycleEquiv i r = (r.val : ZMod k) + i := by
  cases k with
  | zero => exact Fin.elim0 r
  | succ n =>
      change ((ZMod.finEquiv (n + 1)) r) + i = (r.val : ZMod (n + 1)) + i
      congr 1
      apply Fin.ext
      exact (Nat.mod_eq_of_lt r.isLt).symm

omit [NeZero k] in
theorem natCast_ne_zero_of_pos_of_lt {r : Nat} (hr0 : 0 < r) (hrk : r < k) :
    (r : ZMod k) ≠ 0 := by
  intro hzero
  have hdvd : k ∣ r := (ZMod.natCast_eq_zero_iff r k).mp hzero
  exact Nat.not_dvd_of_pos_of_lt hr0 hrk hdvd

def IsFlip (lower upper : InputWord k) (i : ZMod k) : Prop :=
  lower i = false /\ upper i = true /\
    forall j, j ≠ i -> lower j = upper j

omit [NeZero k] in
theorem flip_input_mono {lower upper : InputWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i) :
    forall j, (lower j).toNat <= (upper j).toNat := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [hflip.1, hflip.2.1]
  · rw [hflip.2.2 j hji]

omit [NeZero k] in
theorem compatible_eq_next_of_ne_flip
    {lower upper d : InputWord k} {lo hi : CarryWord k} {i j : ZMod k}
    (hflip : IsFlip lower upper i)
    (hlo : CarryCompatible lower d lo)
    (hhi : CarryCompatible upper d hi)
    (hji : j ≠ i) (heq : hi j <-> lo j) :
    hi (j + 1) <-> lo (j + 1) := by
  rw [hhi j, hlo j, hflip.2.2 j hji, heq]

omit [NeZero k] in
theorem compatible_eq_forward
    {lower upper d : InputWord k} {lo hi : CarryWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (hlo : CarryCompatible lower d lo)
    (hhi : CarryCompatible upper d hi)
    {s : Nat} (hs0 : 0 < s) (_hsk : s <= k)
    (heq : hi (i + (s : ZMod k)) <-> lo (i + (s : ZMod k))) :
    forall n : Nat, s + n <= k ->
      (hi (i + (s + n : Nat)) <-> lo (i + (s + n : Nat))) := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa using heq
  | succ n ih =>
      intro hbound
      have hprevBound : s + n <= k := by omega
      have hprevLt : s + n < k := by omega
      have hprevPos : 0 < s + n := by omega
      have hprev := ih hprevBound
      have hneCast : ((s + n : Nat) : ZMod k) ≠ 0 :=
        natCast_ne_zero_of_pos_of_lt hprevPos hprevLt
      have hne : i + ((s + n : Nat) : ZMod k) ≠ i := by
        intro hEq
        apply hneCast
        apply add_left_cancel (a := i)
        simpa [add_assoc, add_comm, add_left_comm] using hEq
      have hnext := compatible_eq_next_of_ne_flip
        hflip hlo hhi hne (by simpa [Nat.cast_add] using hprev)
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hnext

noncomputable def cyclicPrefix (i : ZMod k) (n : Nat) : Finset (ZMod k) :=
  (Finset.range n).image (fun r => i + ((r + 1 : Nat) : ZMod k))

omit [NeZero k] in
theorem cyclicPrefix_card_le (i : ZMod k) (n : Nat) :
    (cyclicPrefix i n).card <= n := by
  classical
  unfold cyclicPrefix
  simpa using (Finset.card_image_le
    (s := Finset.range n)
    (f := fun r : Nat => i + ((r + 1 : Nat) : ZMod k)))

theorem diffSet_subset_cyclicPrefix_of_eq
    {lower upper d : InputWord k} {lo hi : CarryWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (hlo : CarryCompatible lower d lo)
    (hhi : CarryCompatible upper d hi)
    {s : Nat} (hs0 : 0 < s) (hsk : s <= k)
    (heq : hi (i + (s : ZMod k)) <-> lo (i + (s : ZMod k))) :
    diffSet hi lo ⊆ cyclicPrefix i (s - 1) := by
  classical
  intro j hj
  have hjhi : hi j := by
    simp [diffSet, carrySet] at hj
    exact hj.1
  have hjlo : ¬ lo j := by
    simp [diffSet, carrySet] at hj
    exact hj.2
  let r : Fin k := (cycleEquiv i).symm j
  have hjr : j = i + (r.val : ZMod k) := by
    have h := (cycleEquiv i).apply_symm_apply j
    change cycleEquiv i r = j at h
    rw [cycleEquiv_apply] at h
    simpa [add_comm] using h.symm
  have hr0 : 0 < r.val := by
    by_contra hnot
    have hrzero : r.val = 0 := by omega
    have heqk := compatible_eq_forward hflip hlo hhi hs0 hsk heq (k - s) (by omega)
    have hik : i + ((s + (k - s) : Nat) : ZMod k) = i := by
      rw [show s + (k - s) = k by omega]
      simp
    have hjEq : j = i := by simp [hjr, hrzero]
    rw [hik] at heqk
    rw [hjEq] at hjhi hjlo
    exact hjlo (heqk.mp hjhi)
  have hrs : r.val < s := by
    by_contra hnot
    have hsr : s <= r.val := by omega
    have heqr := compatible_eq_forward hflip hlo hhi hs0 hsk heq
      (r.val - s) (by omega)
    have hsadd : s + (r.val - s) = r.val := by omega
    rw [hsadd] at heqr
    rw [hjr] at hjhi hjlo
    exact hjlo (heqr.mp hjhi)
  unfold cyclicPrefix
  apply Finset.mem_image.mpr
  refine ⟨r.val - 1, Finset.mem_range.mpr (by omega), ?_⟩
  rw [show r.val - 1 + 1 = r.val by omega]
  simpa [add_comm] using hjr.symm

theorem diffSet_card_lt_of_eq
    {lower upper d : InputWord k} {lo hi : CarryWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (hlo : CarryCompatible lower d lo)
    (hhi : CarryCompatible upper d hi)
    {s : Nat} (hs0 : 0 < s) (hsk : s <= k)
    (heq : hi (i + (s : ZMod k)) <-> lo (i + (s : ZMod k))) :
    (diffSet hi lo).card < s := by
  have hsub := diffSet_subset_cyclicPrefix_of_eq hflip hlo hhi hs0 hsk heq
  calc
    (diffSet hi lo).card <= (cyclicPrefix i (s - 1)).card := Finset.card_le_card hsub
    _ <= s - 1 := cyclicPrefix_card_le i (s - 1)
    _ < s := by omega

theorem pivotal_prefix_difference
    {lower upper d : InputWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (m h : Nat) (_hh : 0 < h) (hhk : h < k)
    (hupper : weight (selectedCarry upper d) = m + h)
    (hlower : weight (selectedCarry lower d) <= m) :
    forall s : Nat, 0 < s -> s <= h ->
      selectedCarry upper d (i + (s : ZMod k)) /\
        ¬ selectedCarry lower d (i + (s : ZMod k)) := by
  intro s hs0 hsh
  have hmono : selectedCarry lower d <= selectedCarry upper d :=
    selectedCarry_mono (flip_input_mono hflip)
  have hcompatLo := selectedCarry_compatible lower d
  have hcompatHi := selectedCarry_compatible upper d
  have hne : ¬ (selectedCarry upper d (i + (s : ZMod k)) <->
      selectedCarry lower d (i + (s : ZMod k))) := by
    intro heq
    have hcardLt := diffSet_card_lt_of_eq hflip hcompatLo hcompatHi hs0
      (by omega) heq
    have hweight := weight_eq_add_diff_card hmono
    omega
  have hupOr : selectedCarry upper d (i + (s : ZMod k)) \/
      ¬ selectedCarry upper d (i + (s : ZMod k)) := Classical.em _
  rcases hupOr with hup | hnup
  · refine ⟨hup, ?_⟩
    intro hlo
    exact hne ⟨fun _ => hlo, fun _ => hup⟩
  · have hnlo : ¬ selectedCarry lower d (i + (s : ZMod k)) := by
      intro hlo
      exact hnup (hmono _ hlo)
    exact (hne (iff_of_false hnup hnlo)).elim

theorem full_difference_of_difference_at_flip
    {lower upper d : InputWord k} {lo hi : CarryWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (hlo : CarryCompatible lower d lo)
    (hhi : CarryCompatible upper d hi)
    (hmono : lo <= hi) (hhi_i : hi i) (hlo_i : ¬ lo i) :
    forall j, hi j /\ ¬ lo j := by
  intro j
  let r : Fin k := (cycleEquiv i).symm j
  have hjr : j = i + (r.val : ZMod k) := by
    have h := (cycleEquiv i).apply_symm_apply j
    change cycleEquiv i r = j at h
    rw [cycleEquiv_apply] at h
    simpa [add_comm] using h.symm
  by_cases hr0 : r.val = 0
  · have hjEq : j = i := by simp [hjr, hr0]
    simpa [hjEq] using And.intro hhi_i hlo_i
  · have hrpos : 0 < r.val := by omega
    have hne : ¬ (hi j <-> lo j) := by
      intro heq
      have heqAt : hi (i + (r.val : ZMod k)) <->
          lo (i + (r.val : ZMod k)) := by simpa [hjr] using heq
      have heqk := compatible_eq_forward hflip hlo hhi hrpos r.isLt.le heqAt
        (k - r.val) (by omega)
      have hsum : r.val + (k - r.val) = k := by omega
      rw [hsum] at heqk
      have hik : i + (k : ZMod k) = i := by simp
      rw [hik] at heqk
      exact hlo_i (heqk.mp hhi_i)
    by_cases hhij : hi j
    · refine ⟨hhij, ?_⟩
      intro hloj
      exact hne ⟨fun _ => hloj, fun _ => hhij⟩
    · have hloj : ¬ lo j := by
        intro h
        exact hhij (hmono j h)
      exact (hne (iff_of_false hhij hloj)).elim

omit [NeZero k] in
theorem constant_true_compatible_of_input_ne_target
    {x d : InputWord k} (hne : forall j, x j ≠ d j) :
    CarryCompatible x d (fun _ => True) := by
  intro j
  simp only
  unfold gate
  rw [if_neg (hne j)]

theorem pivotal_flip_is_mismatch
    {lower upper d : InputWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (hnextHi : selectedCarry upper d (i + 1))
    (hnextLo : ¬ selectedCarry lower d (i + 1)) :
    ¬ (selectedCarry upper d i <-> d i = true) := by
  let hi := selectedCarry upper d
  let lo := selectedCarry lower d
  have hmono : lo <= hi := selectedCarry_mono (flip_input_mono hflip)
  have hcompatLo : CarryCompatible lower d lo := selectedCarry_compatible lower d
  have hcompatHi : CarryCompatible upper d hi := selectedCarry_compatible upper d
  intro hmatch
  have hdtrue : d i = true := by
    cases hd : d i with
    | false =>
        have hnotHi : ¬ hi i := by
          intro hhi
          have : d i = true := hmatch.mp hhi
          simp [hd] at this
        have hstep := (hcompatHi i).mp hnextHi
        simp [gate, hflip.2.1, hd, hnotHi] at hstep
    | true => rfl
  have hhi_i : hi i := hmatch.mpr hdtrue
  have hlo_i : ¬ lo i := by
    intro hloi
    have hlonext : lo (i + 1) := (hcompatLo i).mpr (by
      simp [gate, hflip.1, hdtrue, hloi])
    exact hnextLo hlonext
  have hfull := full_difference_of_difference_at_flip
    hflip hcompatLo hcompatHi hmono hhi_i hlo_i
  have hinputNe : forall j, lower j ≠ d j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [hflip.1, hdtrue]
    · intro heq
      have hstates := hfull j
      have hstatesNext := hfull (j + 1)
      have hupperInput : upper j = lower j := (hflip.2.2 j hji).symm
      cases hdj : d j with
      | false =>
          have hnotHiNext : ¬ hi (j + 1) := by
            rw [hcompatHi j]
            simp [gate, hupperInput, heq, hdj]
          exact hnotHiNext hstatesNext.1
      | true =>
          have hLoNext : lo (j + 1) := by
            rw [hcompatLo j]
            simp [gate, heq, hdj]
          exact hstatesNext.2 hLoNext
  have htopCompatible := constant_true_compatible_of_input_ne_target hinputNe
  have htopLe : (fun _ : ZMod k => True) <= lo :=
    compatible_le_selected htopCompatible
  exact hlo_i (htopLe i trivial)

omit [NeZero k] in
theorem pivotal_forced_zero
    {lower upper d : InputWord k} {i : ZMod k}
    {r : Nat} (hr0 : 0 < r) (hrk : r < k)
    (hflip : IsFlip lower upper i)
    (_hcurrHi : selectedCarry upper d (i + (r : ZMod k)))
    (_hcurrLo : ¬ selectedCarry lower d (i + (r : ZMod k)))
    (hnextLo : ¬ selectedCarry lower d (i + (r + 1 : Nat)))
    (hd : d (i + (r : ZMod k)) = true) :
    upper (i + (r : ZMod k)) = false := by
  have hcompatLo := selectedCarry_compatible lower d
  have hne : i + (r : ZMod k) ≠ i := by
    intro heq
    have hcast : (r : ZMod k) ≠ 0 := natCast_ne_zero_of_pos_of_lt hr0 hrk
    apply hcast
    apply add_left_cancel (a := i)
    simpa [add_assoc, add_comm, add_left_comm] using heq
  have hinputs := hflip.2.2 (i + (r : ZMod k)) hne
  cases hx : upper (i + (r : ZMod k)) with
  | false => rfl
  | true =>
      have hlowerInput : lower (i + (r : ZMod k)) = true := by
        rw [hinputs, hx]
      have hlowerNext :
          selectedCarry lower d (i + (r : ZMod k) + 1) :=
        (hcompatLo (i + (r : ZMod k))).mpr (by
          simp [gate, hlowerInput, hd])
      apply (hnextLo (by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hlowerNext)).elim

end LeanCipher.TuDengCyclic

namespace LeanCipher.TuDengCyclic

variable {k : Nat} [NeZero k]

def PivotalConditions (d upper : InputWord k) (c : CarryWord k)
    (i : ZMod k) (h : Nat) : Prop :=
  (¬ (c i ↔ d i = true)) ∧
    (∀ r : Nat, 0 < r → r ≤ h → c (i + (r : ZMod k))) ∧
    (∀ r : Nat, 0 < r → r < h →
      d (i + (r : ZMod k)) = true →
      upper (i + (r : ZMod k)) = false)

theorem pivotal_conditions_of_rank_crossing
    {lower upper d : InputWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (m h : Nat) (hh : 0 < h) (hhk : h < k)
    (hupper : weight (selectedCarry upper d) = m + h)
    (hlower : weight (selectedCarry lower d) ≤ m) :
    PivotalConditions d upper (selectedCarry upper d) i h := by
  have hprefix := pivotal_prefix_difference hflip m h hh hhk hupper hlower
  have hnext := hprefix 1 (by omega) (by omega)
  refine ⟨pivotal_flip_is_mismatch hflip (by simpa using hnext.1)
      (by simpa using hnext.2), ?_, ?_⟩
  · intro r hr0 hrh
    exact (hprefix r hr0 hrh).1
  · intro r hr0 hrh hd
    have hcurr := hprefix r hr0 (by omega)
    have hnext' := hprefix (r + 1) (by omega) (by omega)
    exact pivotal_forced_zero hr0 (by omega) hflip hcurr.1 hcurr.2
      (by simpa [Nat.cast_add, Nat.cast_one] using hnext'.2) hd

omit [NeZero k] in
theorem lower_next_false_at_flip
    {lower upper d : InputWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (hmono : selectedCarry lower d ≤ selectedCarry upper d)
    (hmis : ¬ (selectedCarry upper d i ↔ d i = true))
    (_hnextHi : selectedCarry upper d (i + 1)) :
    ¬ selectedCarry lower d (i + 1) := by
  have hlo := selectedCarry_compatible lower d
  have hhi := selectedCarry_compatible upper d
  cases hd : d i with
  | false =>
      rw [hlo i]
      simp [gate, hflip.1, hd]
  | true =>
      have hnhi : ¬ selectedCarry upper d i := by
        intro h
        exact hmis ⟨fun _ => hd, fun _ => h⟩
      have hnlo : ¬ selectedCarry lower d i := by
        intro h
        exact hnhi (hmono i h)
      rw [hlo i]
      simp [gate, hflip.1, hd, hnlo]

omit [NeZero k] in
theorem lower_next_false_of_prefix
    {lower upper d : InputWord k} {i : ZMod k} {r : Nat}
    (hr0 : 0 < r) (hrk : r < k)
    (hflip : IsFlip lower upper i)
    (hcurrLo : ¬ selectedCarry lower d (i + (r : ZMod k)))
    (hforced : d (i + (r : ZMod k)) = true →
      upper (i + (r : ZMod k)) = false) :
    ¬ selectedCarry lower d (i + (r + 1 : Nat)) := by
  have hcompat := selectedCarry_compatible lower d
  have hne : i + (r : ZMod k) ≠ i := by
    intro heq
    have hcast : (r : ZMod k) ≠ 0 := natCast_ne_zero_of_pos_of_lt hr0 hrk
    apply hcast
    apply add_left_cancel (a := i)
    simpa [add_assoc, add_comm, add_left_comm] using heq
  have hinput := hflip.2.2 (i + (r : ZMod k)) hne
  rw [show i + (r + 1 : Nat) = i + (r : ZMod k) + 1 by
    simp [Nat.cast_add, Nat.cast_one, add_assoc]]
  rw [hcompat (i + (r : ZMod k))]
  cases hd : d (i + (r : ZMod k)) with
  | false => simp [gate, hcurrLo]
  | true =>
      have hupp : upper (i + (r : ZMod k)) = false := hforced hd
      have hlow : lower (i + (r : ZMod k)) = false := by
        rw [hinput, hupp]
      simp [gate, hlow, hcurrLo]

omit [NeZero k] in
theorem prefix_difference_of_pivotal_conditions
    {lower upper d : InputWord k} {i : ZMod k} {h : Nat}
    (hflip : IsFlip lower upper i)
    (_hh : 0 < h) (hhk : h < k)
    (hcond : PivotalConditions d upper (selectedCarry upper d) i h) :
    ∀ r : Nat, 0 < r → r ≤ h →
      selectedCarry upper d (i + (r : ZMod k)) ∧
        ¬ selectedCarry lower d (i + (r : ZMod k)) := by
  have hmono : selectedCarry lower d ≤ selectedCarry upper d :=
    selectedCarry_mono (flip_input_mono hflip)
  intro r
  induction r with
  | zero => omega
  | succ r ih =>
      intro _ hrs
      have hhi : selectedCarry upper d (i + ((r + 1 : Nat) : ZMod k)) :=
        hcond.2.1 (r + 1) (by omega) hrs
      by_cases hr : r = 0
      · subst r
        refine ⟨hhi, ?_⟩
        simpa using lower_next_false_at_flip hflip hmono hcond.1
          (by simpa using hhi)
      · have hrpos : 0 < r := by omega
        have hrh : r ≤ h := by omega
        have hprev := ih hrpos hrh
        refine ⟨hhi, ?_⟩
        exact (by
          simpa [Nat.cast_add, Nat.cast_one] using
            lower_next_false_of_prefix hrpos (by omega) hflip hprev.2
              (hcond.2.2 r hrpos (by omega)))

theorem rank_below_of_pivotal_conditions
    {lower upper d : InputWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (m h : Nat) (hh : 0 < h) (hhk : h < k)
    (hupper : weight (selectedCarry upper d) = m + h)
    (hcond : PivotalConditions d upper (selectedCarry upper d) i h) :
    weight (selectedCarry lower d) ≤ m := by
  have hmono : selectedCarry lower d ≤ selectedCarry upper d :=
    selectedCarry_mono (flip_input_mono hflip)
  have hprefix := prefix_difference_of_pivotal_conditions hflip hh hhk hcond
  have hprefSub : cyclicPrefix i h ⊆
      diffSet (selectedCarry upper d) (selectedCarry lower d) := by
    intro j hj
    simp only [cyclicPrefix, Finset.mem_image, Finset.mem_range] at hj
    obtain ⟨r, hr, rfl⟩ := hj
    have hs := hprefix (r + 1) (by omega) (by omega)
    simp only [diffSet, Finset.mem_sdiff, carrySet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [Nat.cast_add, Nat.cast_one] using hs
  have hprefCard : (cyclicPrefix i h).card = h := by
    unfold cyclicPrefix
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a ha b hb hab
      have ha' : a + 1 < k := by
        have := Finset.mem_range.mp ha
        omega
      have hb' : b + 1 < k := by
        have := Finset.mem_range.mp hb
        omega
      have hcast : ((a + 1 : Nat) : ZMod k) = (b + 1 : Nat) :=
        add_left_cancel hab
      have hmod := (ZMod.natCast_eq_natCast_iff' (a + 1) (b + 1) k).mp hcast
      rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hmod
      omega
  have hdiff : h ≤ (diffSet (selectedCarry upper d)
      (selectedCarry lower d)).card := by
    rw [← hprefCard]
    exact Finset.card_le_card hprefSub
  have hweight := weight_eq_add_diff_card hmono
  omega

theorem rank_crossing_iff_pivotal_conditions
    {lower upper d : InputWord k} {i : ZMod k}
    (hflip : IsFlip lower upper i)
    (m h : Nat) (hh : 0 < h) (hhk : h < k)
    (hupper : weight (selectedCarry upper d) = m + h) :
    weight (selectedCarry lower d) ≤ m ↔
      PivotalConditions d upper (selectedCarry upper d) i h := by
  constructor
  · exact pivotal_conditions_of_rank_crossing hflip m h hh hhk hupper
  · exact rank_below_of_pivotal_conditions hflip m h hh hhk hupper

omit [NeZero k] in
theorem compatible_eq_next_same_input
    {x d : InputWord k} {lo hi : CarryWord k} {j : ZMod k}
    (hlo : CarryCompatible x d lo) (hhi : CarryCompatible x d hi)
    (heq : hi j ↔ lo j) : hi (j + 1) ↔ lo (j + 1) := by
  rw [hhi j, hlo j, heq]

theorem compatible_eq_everywhere_of_eq_at
    {x d : InputWord k} {lo hi : CarryWord k} {i : ZMod k}
    (hlo : CarryCompatible x d lo) (hhi : CarryCompatible x d hi)
    (heq : hi i ↔ lo i) : ∀ j, hi j ↔ lo j := by
  have hforward : ∀ n : Nat, hi (i + (n : ZMod k)) ↔ lo (i + (n : ZMod k)) := by
    intro n
    induction n with
    | zero => simpa using heq
    | succ n ih =>
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
          compatible_eq_next_same_input hlo hhi ih
  intro j
  let r : Fin k := (cycleEquiv i).symm j
  have hjr : j = i + (r.val : ZMod k) := by
    have h := (cycleEquiv i).apply_symm_apply j
    change cycleEquiv i r = j at h
    rw [cycleEquiv_apply] at h
    simpa [add_comm] using h.symm
  rw [hjr]
  exact hforward r.val

theorem compatible_eq_or_full_difference
    {x d : InputWord k} {lo hi : CarryWord k}
    (hlo : CarryCompatible x d lo) (hhi : CarryCompatible x d hi)
    (hmono : lo ≤ hi) :
    lo = hi ∨ ∀ j, hi j ∧ ¬ lo j := by
  classical
  by_cases heq : lo = hi
  · exact Or.inl heq
  · right
    intro j
    have hnotIff : ¬ (hi j ↔ lo j) := by
      intro hj
      apply heq
      funext q
      exact propext (compatible_eq_everywhere_of_eq_at hlo hhi hj q).symm
    by_cases hhij : hi j
    · refine ⟨hhij, ?_⟩
      intro hloj
      exact hnotIff ⟨fun _ => hloj, fun _ => hhij⟩
    · have hnlo : ¬ lo j := fun hloj => hhij (hmono j hloj)
      exact (hnotIff (iff_of_false hhij hnlo)).elim

noncomputable def inputWeight (x : InputWord k) : Nat :=
  ((Finset.univ : Finset (ZMod k)).filter fun j => x j = true).card

theorem compatible_bad_eq_selected
    {x d : InputWord k} {c : CarryWord k}
    (hc : CarryCompatible x d c) (hbad : inputWeight d < weight c) :
    c = selectedCarry x d := by
  have hsel := selectedCarry_compatible x d
  have hle : c ≤ selectedCarry x d := compatible_le_selected hc
  rcases compatible_eq_or_full_difference hc hsel hle with heq | hfull
  · exact heq
  · have hcEmpty : carrySet c = ∅ := by
      ext j
      simp [carrySet, hfull j |>.2]
    have hcZero : weight c = 0 := by simp [weight, hcEmpty]
    omega

omit [NeZero k] in
theorem compatible_iff_of_support
    {x d : InputWord k} {c : CarryWord k}
    (hsupport : ∀ j, (c j ↔ d j = true) → (c (j + 1) ↔ c j)) :
    CarryCompatible x d c ↔
      ∀ j, ¬ (c j ↔ d j = true) → ((x j = true) ↔ c (j + 1)) := by
  constructor
  · intro hc j hmis
    exact compatible_mismatch hc hmis
  · intro hmis j
    have hs := hsupport j
    have hm := hmis j
    by_cases hcj : c j <;> by_cases hcnext : c (j + 1) <;>
      cases hx : x j <;> cases hd : d j <;>
      simp_all [gate]

end LeanCipher.TuDengCyclic

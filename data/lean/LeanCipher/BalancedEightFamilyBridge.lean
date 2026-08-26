import LeanCipher.BalancedEightCertificates

namespace LeanCipher.BalancedEightCertificates

/-!
# Structural bridges for the declared local-table families

The executable data stores one family for each `(weight, profile)` key.
This file exposes ordinary list-theoretic consequences of that representation:
an entry remembers both its profile and its row, and positive weight-61 and
weight-63 counts with corresponding entries rule out a missing family.
-/

def familyKey (family : Family) : Nat × Profile :=
  (family.weight, family.profile)

theorem declared_family_keys_nodup :
    (declaredFamilies.map familyKey).Nodup := by
  native_decide

private theorem declared_family_key_injective
    {left right : Family}
    (hleft : left ∈ declaredFamilies)
    (hright : right ∈ declaredFamilies)
    (hweight : left.weight = right.weight)
    (hprofile : left.profile = right.profile) :
    left = right := by
  apply List.inj_on_of_nodup_map declared_family_keys_nodup hleft hright
  exact Prod.ext hweight hprofile

theorem profile_mem_profiles59_of_declaredEntry
    {profile : Profile} {table : LocalTable}
    (hentry : (59, profile, table) ∈ declaredEntries) :
    profile ∈ profiles59 := by
  unfold declaredEntries at hentry
  rcases List.mem_flatMap.mp hentry with ⟨family, hfamily, hrowEntry⟩
  rcases List.mem_map.mp hrowEntry with ⟨row, _hrow, heq⟩
  have hweight : family.weight = 59 :=
    congrArg (fun entry : TableEntry => entry.1) heq
  have hprofile : family.profile = profile :=
    congrArg (fun entry : TableEntry => entry.2.1) heq
  apply List.mem_map.mpr
  refine ⟨family, ?_, hprofile⟩
  exact List.mem_filter.mpr ⟨hfamily, by simpa using hweight⟩

theorem table_mem_rowsFor_of_declaredEntry
    {weight : Nat} {profile : Profile} {table : LocalTable}
    (hentry : (weight, profile, table) ∈ declaredEntries) :
    table ∈ rowsFor weight profile := by
  unfold declaredEntries at hentry
  rcases List.mem_flatMap.mp hentry with ⟨family, hfamily, hrowEntry⟩
  rcases List.mem_map.mp hrowEntry with ⟨row, hrow, heq⟩
  have hweight : family.weight = weight :=
    congrArg (fun entry : TableEntry => entry.1) heq
  have hprofile : family.profile = profile :=
    congrArg (fun entry : TableEntry => entry.2.1) heq
  have htable : row = table :=
    congrArg (fun entry : TableEntry => entry.2.2) heq
  have hfamilyMatches :
      (family.weight = weight && family.profile = profile) = true := by
    simp [hweight, hprofile]
  unfold rowsFor
  cases hfind : declaredFamilies.find? (fun candidate =>
      candidate.weight = weight && candidate.profile = profile) with
  | none =>
      exact False.elim
        ((List.find?_eq_none.mp hfind family hfamily) hfamilyMatches)
  | some found =>
      have hfoundMem : found ∈ declaredFamilies :=
        List.mem_of_find?_eq_some hfind
      have hfoundMatches :
          found.weight = weight ∧ found.profile = profile := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using
          List.find?_some hfind
      have hfoundEq : found = family :=
        declared_family_key_injective hfoundMem hfamily
          (hfoundMatches.1.trans hweight.symm)
          (hfoundMatches.2.trans hprofile.symm)
      change table ∈ found.rows
      rw [hfoundEq]
      simpa [htable] using hrow

theorem rowsFor_isEmpty_eq_false_of_declaredEntry
    {weight : Nat} {profile : Profile} {table : LocalTable}
    (hentry : (weight, profile, table) ∈ declaredEntries) :
    (rowsFor weight profile).isEmpty = false := by
  apply List.isEmpty_eq_false_iff_exists_mem.mpr
  exact ⟨table, table_mem_rowsFor_of_declaredEntry hentry⟩

theorem missingFamily_eq_false_of_declaredEntry_providers
    {profile : Profile}
    (h61 : 0 < profile.n12 →
      ∃ table, (61, profile, table) ∈ declaredEntries)
    (h63 : 0 < profile.n4 →
      ∃ table, (63, profile, table) ∈ declaredEntries) :
    missingFamily profile = false := by
  by_cases hn12 : 0 < profile.n12
  · rcases h61 hn12 with ⟨table61, hentry61⟩
    have hrows61 : (rowsFor 61 profile).isEmpty = false :=
      rowsFor_isEmpty_eq_false_of_declaredEntry hentry61
    by_cases hn4 : 0 < profile.n4
    · rcases h63 hn4 with ⟨table63, hentry63⟩
      have hrows63 : (rowsFor 63 profile).isEmpty = false :=
        rowsFor_isEmpty_eq_false_of_declaredEntry hentry63
      simp [missingFamily, hn12, hn4, hrows61, hrows63]
    · simp [missingFamily, hn12, hn4, hrows61]
  · by_cases hn4 : 0 < profile.n4
    · rcases h63 hn4 with ⟨table63, hentry63⟩
      have hrows63 : (rowsFor 63 profile).isEmpty = false :=
        rowsFor_isEmpty_eq_false_of_declaredEntry hentry63
      simp [missingFamily, hn12, hn4, hrows63]
    · simp [missingFamily, hn12, hn4]

end LeanCipher.BalancedEightCertificates

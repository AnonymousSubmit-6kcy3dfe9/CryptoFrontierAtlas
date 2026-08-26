import LeanCipher.BalancedEightFarkasSound

namespace LeanCipher.BalancedEightCertificates

/-!
# Elimination of the weight-59 spectral profiles

This file combines the checked finite partition with the soundness of the
integer Farkas certificates.  Thus a profile in the weight-59 enumeration
which has all required local families and whose global multiplicity system
has a nonnegative rational solution must be one of the thirteen declared
survivors.
-/

theorem not_mem_certificateProfiles_of_nonnegative_rational_solution
    {profile : Profile}
    (hsolution : HasNonnegativeRationalSolution profile) :
    profile ∉ certificateProfiles := by
  intro hprofile
  rcases List.mem_map.mp hprofile with ⟨certificate, hcertificate, heq⟩
  apply declared_farkas_certificates_exclude_nonnegative_rational_solutions
    certificate hcertificate
  simpa [heq] using hsolution

theorem mem_computedSurvivors_of_profile_constraints
    {profile : Profile}
    (hprofile : profile ∈ profiles59)
    (hfamilies : missingFamily profile = false)
    (hsolution : HasNonnegativeRationalSolution profile) :
    profile ∈ computedSurvivors := by
  have hcandidate : profile ∈ candidateProfiles := by
    simp [candidateProfiles, hprofile, hfamilies]
  have hnotCertificate : profile ∉ certificateProfiles :=
    not_mem_certificateProfiles_of_nonnegative_rational_solution hsolution
  simp [computedSurvivors, hcandidate, hnotCertificate]

theorem mem_declaredSurvivors_of_profile_constraints
    {profile : Profile}
    (hprofile : profile ∈ profiles59)
    (hfamilies : missingFamily profile = false)
    (hsolution : HasNonnegativeRationalSolution profile) :
    profile ∈ declaredSurvivors := by
  have hsurvivor := mem_computedSurvivors_of_profile_constraints
    hprofile hfamilies hsolution
  rw [weight59_profiles_partition.2.2.2.2.2.1] at hsurvivor
  exact hsurvivor

theorem weight59_profile_elimination
    {profile : Profile} (hprofile : profile ∈ profiles59) :
    missingFamily profile = true ∨
      ¬ HasNonnegativeRationalSolution profile ∨
      profile ∈ declaredSurvivors := by
  by_cases hfamilies : missingFamily profile = true
  · exact Or.inl hfamilies
  · have hfamiliesFalse : missingFamily profile = false := by
      exact Bool.eq_false_of_not_eq_true hfamilies
    by_cases hsolution : HasNonnegativeRationalSolution profile
    · exact Or.inr (Or.inr
        (mem_declaredSurvivors_of_profile_constraints
          hprofile hfamiliesFalse hsolution))
    · exact Or.inr (Or.inl hsolution)

end LeanCipher.BalancedEightCertificates

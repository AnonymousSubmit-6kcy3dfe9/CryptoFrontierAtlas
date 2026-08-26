import LeanCipher.BalancedEightCertificates

open scoped BigOperators

namespace LeanCipher.BalancedEightCertificates

def dot12Rat (left right : List Int) : Rat :=
  ∑ index : Fin 12, (valueAt left index : Rat) * (valueAt right index : Rat)

theorem int_dot12_cast_rat (left right : List Int) :
    (dot12 left right : Rat) = dot12Rat left right := by
  simp only [dot12, dot12Rat]
  push_cast
  rfl

def HasNonnegativeRationalSolution (profile : Profile) : Prop :=
  ∃ multiplicity : Fin (columns profile).length -> Rat,
    (∀ index, 0 <= multiplicity index) ∧
    ∀ coordinate : Fin 12,
      (∑ index, multiplicity index *
        (valueAt ((columns profile).get index) coordinate : Rat)) =
          (valueAt (rhs profile) coordinate : Rat)

theorem validCertificate_excludes_nonnegative_rational_solution
    (certificate : IntCertificate) (hValid : ValidCertificate certificate) :
    ¬ HasNonnegativeRationalSolution certificate.profile := by
  rintro ⟨multiplicity, hNonnegative, hSystem⟩
  rcases hValid with ⟨hScale, _hLength, _hCandidate, hRhs, hColumns⟩
  have hIdentity :
      (dot12 (rhs certificate.profile) certificate.z : Rat) =
        ∑ index : Fin (columns certificate.profile).length,
          multiplicity index *
            (dot12 ((columns certificate.profile).get index) certificate.z : Rat) := by
    rw [int_dot12_cast_rat]
    simp only [dot12Rat]
    calc
      (∑ coordinate : Fin 12,
          (valueAt (rhs certificate.profile) coordinate : Rat) *
            (valueAt certificate.z coordinate : Rat)) =
          ∑ coordinate : Fin 12,
            (∑ index : Fin (columns certificate.profile).length,
              multiplicity index *
                (valueAt ((columns certificate.profile).get index) coordinate : Rat)) *
              (valueAt certificate.z coordinate : Rat) := by
                apply Finset.sum_congr rfl
                intro coordinate _
                rw [hSystem coordinate]
      _ = ∑ index : Fin (columns certificate.profile).length,
          ∑ coordinate : Fin 12,
            (multiplicity index *
              (valueAt ((columns certificate.profile).get index) coordinate : Rat)) *
                (valueAt certificate.z coordinate : Rat) := by
                  simp_rw [Finset.sum_mul]
                  exact Finset.sum_comm
      _ = ∑ index : Fin (columns certificate.profile).length,
          multiplicity index *
            (∑ coordinate : Fin 12,
              (valueAt ((columns certificate.profile).get index) coordinate : Rat) *
                (valueAt certificate.z coordinate : Rat)) := by
                  apply Finset.sum_congr rfl
                  intro index _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro coordinate _
                  ring
      _ = ∑ index : Fin (columns certificate.profile).length,
          multiplicity index *
            (dot12 ((columns certificate.profile).get index) certificate.z : Rat) := by
              apply Finset.sum_congr rfl
              intro index _
              rw [int_dot12_cast_rat]
              rfl
  have hRightNonnegative :
      0 <= ∑ index : Fin (columns certificate.profile).length,
        multiplicity index *
          (dot12 ((columns certificate.profile).get index) certificate.z : Rat) := by
    exact Finset.sum_nonneg fun index _ =>
      mul_nonneg (hNonnegative index) (by exact_mod_cast hColumns index)
  have hLeftNegative :
      (dot12 (rhs certificate.profile) certificate.z : Rat) < 0 := by
    rw [hRhs]
    exact_mod_cast (by omega : -(certificate.scale : Int) < 0)
  linarith

theorem declared_farkas_certificates_exclude_nonnegative_rational_solutions :
    ∀ certificate ∈ declaredCertificates,
      ¬ HasNonnegativeRationalSolution certificate.profile := by
  intro certificate hCertificate
  exact validCertificate_excludes_nonnegative_rational_solution certificate
    (all_integer_farkas_certificates_valid certificate hCertificate)

end LeanCipher.BalancedEightCertificates

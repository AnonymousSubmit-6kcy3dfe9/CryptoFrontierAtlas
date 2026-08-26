import LeanCipher.TuDengGenerated

open scoped BigOperators

namespace LeanCipher

open GeneratedVerifiedLemmas

/-!
The exact pair-count reduction from Proposition 4.1 of the manuscript.
For `M = 2^k - 1`, the bijection sends a pair `(a,b)` to `x = M-a`.
The value `x = 0` is retained in `circularDecreaseCount`, but the strict
weight inequality excludes it.
-/
theorem tuDeng_pair_count_eq_circular_decrease_count
    {k t : Nat}
    (hk : 2 <= k)
    (ht_pos : 1 <= t)
    (ht_upper : t <= 2 ^ k - 2) :
    tuDengCount k t = circularDecreaseCount k t := by
  classical
  let M := 2 ^ k - 1
  have hMpos : 0 < M := by
    dsimp [M]
    exact two_pow_sub_one_pos (by omega)
  rw [tu_deng_count_eq_explicit_bounded_pair_filter hk ht_pos ht_upper]
  unfold circularDecreaseCount
  apply Finset.card_bij (fun ab _ => M - ab.1)
  · intro ab hab
    simp only [Finset.mem_filter] at hab
    rcases hab with ⟨habRange, ha, hb, hcong, hweight⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    have haM : ab.1 <= M - 1 := by omega
    have hbM : ab.2 <= M - 1 := by omega
    have hb' : ab.2 < M := by omega
    have htM : t <= M - 1 := by
      dsimp [M]
      exact ht_upper
    have hcases : ab.1 + ab.2 = t ∨ ab.1 + ab.2 = t + M := by
      dsimp [M] at haM hbM htM ⊢
      apply tu_deng_sum_representative_dichotomy k t ab.1 ab.2 hk ht_pos ht_upper
      · exact haM
      · exact hbM
      · simpa [Nat.ModEq] using hcong
    have hxpow : M - ab.1 < 2 ^ k := by
      have := Finset.mem_range.mp (Finset.mem_product.mp habRange).1
      dsimp [M]
      omega
    refine ⟨hxpow, ?_⟩
    unfold circularDecrease circularAdd
    have hcomp := binaryWeightUpTo_complement (k := k) (n := ab.1) (by
      dsimp [M] at haM ⊢
      omega)
    have hadd : ((M - ab.1 + t) % M) = ab.2 := by
      rcases hcases with hsum | hsum
      · have harg : M - ab.1 + t = M + ab.2 := by omega
        rw [harg]
        simp [Nat.mod_eq_of_lt hb']
      · have harg : M - ab.1 + t = ab.2 := by omega
        rw [harg, Nat.mod_eq_of_lt hb']
    rw [show 2 ^ k - 1 = M by rfl, hadd]
    dsimp [M] at hcomp ⊢
    omega
  · intro ab1 hab1 ab2 hab2 heq
    simp only [Finset.mem_filter] at hab1 hab2
    rcases hab1 with ⟨_, ha1, hb1, hcong1, _⟩
    rcases hab2 with ⟨_, ha2, hb2, hcong2, _⟩
    have haeq : ab1.1 = ab2.1 := by
      dsimp [M] at heq
      omega
    have hbeq : ab1.2 = ab2.2 := by
      have habModeq : Nat.ModEq M (ab1.1 + ab1.2) (ab2.1 + ab2.2) := by
        dsimp [M]
        exact hcong1.trans hcong2.symm
      rw [haeq] at habModeq
      have hbModeq : Nat.ModEq M ab1.2 ab2.2 :=
        Nat.ModEq.add_left_cancel (Nat.ModEq.refl ab2.1) habModeq
      apply hbModeq.eq_of_lt_of_lt
      · dsimp [M]
        omega
      · dsimp [M]
        omega
    exact Prod.ext haeq hbeq
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    rcases hx with ⟨hxpow, hxdec⟩
    have hxzero : x ≠ 0 := by
      intro hx0
      subst x
      exact circular_zero_not_decrease hxdec
    have hxM : x <= M := by
      dsimp [M]
      omega
    let a := M - x
    let b := (x + t) % M
    have haM : a < M := by
      dsimp [a]
      omega
    have hbM : b < M := by
      dsimp [b]
      exact Nat.mod_lt _ hMpos
    refine ⟨(a, b), ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Finset.mem_range.mpr (by omega)⟩,
        by dsimp [M] at haM ⊢; omega,
        by dsimp [M] at hbM ⊢; omega, ?_, ?_⟩
      · have htM : t < M := by
          dsimp [M]
          omega
        have hbdef : b = (x + t) % M := rfl
        have hbModeq : Nat.ModEq M b (x + t) := by
          change b % M = (x + t) % M
          rw [Nat.mod_eq_of_lt hbM, hbdef]
        have haddModeq := hbModeq.add_left a
        have hax : a + x = M := by
          dsimp [a]
          omega
        change (a + b) % M = t % M
        calc
          (a + b) % M = (a + (x + t)) % M := haddModeq
          _ = (M + t) % M := by rw [← Nat.add_assoc, hax]
          _ = t % M := by simp
      · unfold circularDecrease circularAdd at hxdec
        rw [show 2 ^ k - 1 = M by rfl] at hxdec
        have hbdef : b = (x + t) % M := rfl
        rw [← hbdef] at hxdec
        have hcomp := binaryWeightUpTo_complement (k := k) (n := x) (by
          dsimp [M] at hxM ⊢
          exact hxM)
        change binaryWeightUpTo k a + binaryWeightUpTo k b < k
        dsimp [a, M]
        omega
    · dsimp [a]
      exact Nat.sub_sub_self hxM

end LeanCipher

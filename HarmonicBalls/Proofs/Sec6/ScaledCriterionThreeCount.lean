import HarmonicBalls.Proofs.Sec6.CriterionThreeFromPrevalence

/-! # Scaling the radius count in the third criterion -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- A normalized seven-adic subrange count gives the radius count required in
the third criterion at any positive outer radius. -/
theorem scaled_criterionThree_count_of_subrange
    {μ : Measure ℂ} {a b c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    {n : ℕ} (hn : 9 ≤ n) {z : ℂ}
    (h : c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ (s * r) z a b}.ncard : ℝ)) :
    c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  let ε := dyadicScale n
  have hε : 0 < ε := dyadicScale_pos n
  have hε1 : ε ≤ 1 := by dsimp [ε, dyadicScale]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hsqrt := sqrt_dyadicScale_le_one_twentieth hn
  let T : Set ℝ := {r | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
    (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ (s * r) z a b}
  let U : Set ℝ := {r | r ∈ Icc (ε * s) (Real.sqrt ε * s) ∧
    (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}
  have hfin : U.Finite := by
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := s) (lo := ε * s)
      (by norm_num) (by norm_num) (mul_pos hε hs) fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨k, hk⟩
  have hinj : Function.Injective (fun r : ℝ => s * r) := by
    intro x y hxy
    exact mul_left_cancel₀ hs.ne' hxy
  have hsub : (fun r : ℝ => s * r) '' T ⊆ U := by
    rintro r ⟨t, ht, rfl⟩
    have ht_sqrt : t ≤ Real.sqrt ε := ht.1.2.trans (by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num))
    obtain ⟨k, hk⟩ := ht.2.1
    have hk1 : 1 ≤ k := by
      by_contra hbad
      have : k = 0 := by omega
      subst k
      simp only [pow_zero] at hk
      have : Real.sqrt ε ≤ (1 / 20 : ℝ) := hsqrt
      linarith
    refine ⟨⟨?_, ?_⟩, ⟨k, hk1, by rw [hk]⟩, ht.2.2⟩
    · nlinarith [mul_le_mul_of_nonneg_left ht.1.1 hs.le]
    · nlinarith [mul_le_mul_of_nonneg_left ht_sqrt hs.le]
  have hcard : T.ncard ≤ U.ncard := by
    calc
      T.ncard = ((fun r : ℝ => s * r) '' T).ncard := hinj.injOn.ncard_image.symm
      _ ≤ U.ncard := Set.ncard_le_ncard hsub hfin
  exact ((logb_neg_half_le (by norm_num) hc hε hε1).trans h).trans (by exact_mod_cast hcard)

end HarmonicBalls.Section6

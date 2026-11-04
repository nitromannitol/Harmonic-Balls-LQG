import HarmonicBalls.Proofs.Sec8.LogarithmicCutoffEnergy

/-! # Weighted energy of the inner logarithmic cutoff

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real ContDiff
namespace HarmonicBalls

/-- The two Cartesian directional derivatives are bounded by twice the squared operator norm. -/
theorem dirichlet_derivatives_le_opNorm_sq (L : ℂ →L[ℝ] ℝ) :
    (L 1) ^ 2 + (L Complex.I) ^ 2 ≤ 2 * ‖L‖ ^ 2 := by
  have h1 : ‖L 1‖ ≤ ‖L‖ := by simpa using L.le_opNorm (1 : ℂ)
  have hI : ‖L Complex.I‖ ≤ ‖L‖ := by simpa using L.le_opNorm Complex.I
  have h1' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg L)).2 h1
  have hI' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg L)).2 hI
  simp only [Real.norm_eq_abs, sq_abs] at h1' hI'
  linarith

/-- The weighted inner cutoff energy tends to zero for every continuous weight. -/
theorem tendsto_integral_weighted_logarithmicInnerCutoff_gradient (u : ℂ → ℝ)
    (hu : Continuous u) :
    Tendsto (fun n : ℕ => ∫ z : ℂ, (u z) ^ 2 *
      ((fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hu.continuousOn
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖u z‖ ≤ B := by
    intro z hz
    exact (hC z (by simpa only [mem_closedBall, dist_zero_right] using hz)).trans (le_max_left _ _)
  have hpoint (n : ℕ) (z : ℂ) : (u z) ^ 2 *
      ((fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2) ≤
      (2 * B ^ 2) * ‖fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z‖ ^ 2 := by
    by_cases hz : ‖z‖ ≤ 1
    · have hu' := (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound z hz)
      simp only [Real.norm_eq_abs, sq_abs] at hu'
      have hd := dirichlet_derivatives_le_opNorm_sq (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z)
      have hmul := mul_le_mul hu' hd (by positivity : 0 ≤ (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1)^2 + (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I)^2) (sq_nonneg B)
      nlinarith
    · have hexp : Real.exp (-((n : ℝ) + 1)) < ‖z‖ := by
        have he : Real.exp (-((n : ℝ) + 1)) ≤ 1 := by
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
          have he := Real.exp_le_exp.mpr (show -((n : ℝ) + 1) ≤ 0 by linarith)
          simpa only [Real.exp_zero] using he
        exact he.trans_lt (lt_of_not_ge hz)
      have hd := fderiv_logarithmicInnerCutoff_eq_zero_of_outer (by positivity) hexp
      simp [hd]
  have hlim : Tendsto (fun n : ℕ => (2 * B ^ 2) *
      ∫ z : ℂ, ‖fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z‖ ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_integral_logarithmicInnerCutoff_gradient_sq.const_mul (2 * B ^ 2)
  apply squeeze_zero (fun n => integral_nonneg fun z => mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))) _ hlim
  intro n
  obtain ⟨D, hD0, hD⟩ := exists_bound_fderiv_smoothTransition
  have hi := integrable_logarithmicInnerCutoff_gradient_sq (t := (n + 1 : ℝ)) (C := D) (by positivity) hD0 hD
  have hd : Continuous (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ))) :=
    (contDiff_logarithmicInnerCutoff (by positivity)).continuous_fderiv (by norm_num)
  have hc : Continuous (fun z : ℂ => (u z) ^ 2 *
      ((fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) := by
    exact (hu.pow 2).mul (((hd.clm_apply continuous_const).pow 2).add
      ((hd.clm_apply continuous_const).pow 2))
  have hiw : Integrable (fun z : ℂ => (u z) ^ 2 *
      ((fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) := by
    apply Integrable.mono' (hi.const_mul (2 * B ^ 2)) hc.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))]
    exact hpoint n z
  rw [← integral_const_mul]
  exact integral_mono_ae hiw (hi.const_mul _) (Filter.Eventually.of_forall (hpoint n))
/-- The logarithmic potential has vanishing weighted inner cutoff energy. -/
theorem tendsto_integral_planarLogPotential_innerCutoff_gradient {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) :
    Tendsto (fun n : ℕ => ∫ z : ℂ, (planarLogPotential φ z) ^ 2 *
      ((fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) atTop (𝓝 0) :=
  tendsto_integral_weighted_logarithmicInnerCutoff_gradient _
    (contDiff_planarLogPotential hφ).continuous

end HarmonicBalls

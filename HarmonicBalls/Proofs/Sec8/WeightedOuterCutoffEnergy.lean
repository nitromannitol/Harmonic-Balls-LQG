import HarmonicBalls.Proofs.Sec8.OuterCutoff

/-! # Weighted energy of the outer cutoff

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real ContDiff
namespace HarmonicBalls

/-- If a continuous weight vanishes at infinity, its outer-cutoff energy vanishes. -/
theorem tendsto_integral_weighted_outerCutoff_gradient (u : ℂ → ℝ) (hu : Continuous u)
    (hvanish : Tendsto u (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ z : ℂ, (u z) ^ 2 *
      ((fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) atTop (𝓝 0) := by
  let K : ℝ := ∫ z : ℂ, ‖fderiv ℝ outerBump z‖ ^ 2
  have hK : 0 ≤ K := integral_nonneg fun z => sq_nonneg _
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun z =>
      mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  · intro ε hε
    let δ : ℝ := min 1 (ε / (2 * (K + 1)))
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ ≤ ε / (2 * (K + 1)) := min_le_right _ _
    have hsmall : ∀ᶠ z : ℂ in cocompact ℂ, ‖u z‖ < δ := by
      have ht : Tendsto (fun z => ‖u z‖) (cocompact ℂ) (𝓝 0) := by
        simpa using hvanish.norm
      exact ht.eventually (eventually_lt_nhds hδ)
    obtain ⟨r, hr⟩ := (Metric.mem_cocompact_iff_closedBall_compl_subset (0 : ℂ)).1 hsmall
    have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    filter_upwards [hcast.eventually (eventually_ge_atTop (r + 1))] with n hn
    have hpoint (z : ℂ) : (u z) ^ 2 *
        ((fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
          (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2) ≤
        (2 * δ) * ‖fderiv ℝ (outerCutoff (n + 1 : ℝ)) z‖ ^ 2 := by
      by_cases hz : ‖z‖ < ((n : ℝ) + 1)
      · have hd := fderiv_outerCutoff_eq_zero_of_inner (R := (n + 1 : ℝ)) (by positivity) hz
        simp [hd]
      · have hzr : r < ‖z‖ := by linarith [le_of_not_gt hz]
        have huδ : ‖u z‖ < δ := hr (show z ∉ closedBall (0 : ℂ) r by
          simpa only [mem_closedBall, dist_zero_right, not_le] using hzr)
        have hnon : 0 ≤ ‖u z‖ := norm_nonneg _
        have hu2 : (u z) ^ 2 ≤ δ := by
          have : ‖u z‖ ^ 2 = (u z) ^ 2 := by simp
          rw [← this]
          nlinarith
        have hd := dirichlet_derivatives_le_opNorm_sq (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z)
        have hmul := mul_le_mul hu2 hd
          (show 0 ≤ (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
            (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2 by positivity) hδ.le
        nlinarith
    have hi := integrable_outerCutoff_gradient_sq (R := (n + 1 : ℝ)) (by positivity)
    have hc : Continuous (fderiv ℝ (outerCutoff (n + 1 : ℝ))) :=
      (contDiff_outerCutoff _).continuous_fderiv (by norm_num)
    have hη := hasCompactSupport_outerCutoff (R := (n + 1 : ℝ)) (by positivity)
    have hc1 : HasCompactSupport (fun z : ℂ => (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2) := by
      apply (hη.fderiv_apply ℝ 1).mono'
      intro z hz
      apply subset_tsupport
      simp only [Function.mem_support] at hz ⊢
      intro hzero
      exact hz (by simp [hzero])
    have hcI : HasCompactSupport (fun z : ℂ => (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2) := by
      apply (hη.fderiv_apply ℝ Complex.I).mono'
      intro z hz
      apply subset_tsupport
      simp only [Function.mem_support] at hz ⊢
      intro hzero
      exact hz (by simp [hzero])
    have hiw : Integrable (fun z : ℂ => (u z) ^ 2 *
        ((fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
          (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) :=
      ((hu.pow 2).mul (((hc.clm_apply continuous_const).pow 2).add
        ((hc.clm_apply continuous_const).pow 2))).integrable_of_hasCompactSupport (hc1.add hcI).mul_left
    have hb : (∫ z : ℂ, (u z) ^ 2 *
        ((fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
          (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) ≤ (2 * δ) * K := by
      calc
        _ ≤ ∫ z : ℂ, (2 * δ) * ‖fderiv ℝ (outerCutoff (n + 1 : ℝ)) z‖ ^ 2 :=
          integral_mono_ae hiw (hi.const_mul _) (Filter.Eventually.of_forall hpoint)
        _ = (2 * δ) * K := by rw [integral_const_mul, integral_outerCutoff_energy (by positivity)]
    have hfinal : (2 * δ) * K < ε := by
      have hden : 0 < 2 * (K + 1) := by positivity
      have := (le_div_iff₀ hden).1 hδε
      nlinarith
    exact hb.trans_lt hfinal
/-- A mean-zero logarithmic potential has vanishing outer cutoff energy. -/
theorem tendsto_integral_planarLogPotential_outerCutoff_gradient {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : ∫ z, φ z = 0) :
    Tendsto (fun n : ℕ => ∫ z : ℂ, (planarLogPotential φ z) ^ 2 *
      ((fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) atTop (𝓝 0) :=
  tendsto_integral_weighted_outerCutoff_gradient _ (contDiff_planarLogPotential hφ).continuous
    (tendsto_planarLogPotential_cocompact hφ.1.continuous hφ.2.1 hφzero)

end HarmonicBalls

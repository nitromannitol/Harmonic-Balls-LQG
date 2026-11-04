import HarmonicBalls.Proofs.Sec8.PuncturedCutoff
/-! # Weighted energy of punctured cutoffs

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real ContDiff
namespace HarmonicBalls

theorem hasCompactSupport_fderiv_logarithmicInnerCutoff {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (fderiv ℝ (logarithmicInnerCutoff t)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 1)
  intro z hz
  by_contra hn
  have hzgt : 1 < ‖z‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  have he : Real.exp (-t) < ‖z‖ := by
    have he' := Real.exp_le_exp.mpr (show -t ≤ (0 : ℝ) by linarith)
    have he'' : Real.exp (-t) ≤ 1 := by simpa only [Real.exp_zero] using he'
    exact he''.trans_lt hzgt
  exact hz (fderiv_logarithmicInnerCutoff_eq_zero_of_outer ht he)

theorem integrable_weighted_logarithmicInnerCutoff_gradient (u : ℂ → ℝ) (hu : Continuous u)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℂ => (u z) ^ 2 *
      ((fderiv ℝ (logarithmicInnerCutoff t) z 1) ^ 2 +
        (fderiv ℝ (logarithmicInnerCutoff t) z Complex.I) ^ 2)) := by
  have hc : Continuous (fderiv ℝ (logarithmicInnerCutoff t)) :=
    (contDiff_logarithmicInnerCutoff ht).continuous_fderiv (by norm_num)
  have hs := hasCompactSupport_fderiv_logarithmicInnerCutoff ht
  have hv (v : ℂ) : HasCompactSupport (fun z => (fderiv ℝ (logarithmicInnerCutoff t) z v) ^ 2) := by
    apply hs.mono'
    intro z hz
    apply subset_tsupport
    simp only [Function.mem_support] at hz ⊢
    intro hzero
    exact hz (by simp [hzero])
  exact ((hu.pow 2).mul (((hc.clm_apply continuous_const).pow 2).add
    ((hc.clm_apply continuous_const).pow 2))).integrable_of_hasCompactSupport ((hv 1).add (hv Complex.I)).mul_left
theorem integrable_weighted_outerCutoff_gradient (u : ℂ → ℝ) (hu : Continuous u)
    {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : ℂ => (u z) ^ 2 *
      ((fderiv ℝ (outerCutoff R) z 1) ^ 2 +
        (fderiv ℝ (outerCutoff R) z Complex.I) ^ 2)) := by
  have hc : Continuous (fderiv ℝ (outerCutoff R)) :=
    (contDiff_outerCutoff R).continuous_fderiv (by norm_num)
  have hs : HasCompactSupport (fderiv ℝ (outerCutoff R)) :=
    (hasCompactSupport_outerCutoff hR.ne').fderiv (𝕜 := ℝ)
  have hv (v : ℂ) : HasCompactSupport (fun z => (fderiv ℝ (outerCutoff R) z v) ^ 2) := by
    apply hs.mono'
    intro z hz
    apply subset_tsupport
    simp only [Function.mem_support] at hz ⊢
    intro hzero
    exact hz (by simp [hzero])
  exact ((hu.pow 2).mul (((hc.clm_apply continuous_const).pow 2).add
    ((hc.clm_apply continuous_const).pow 2))).integrable_of_hasCompactSupport ((hv 1).add (hv Complex.I)).mul_left
theorem fderiv_puncturedCutoff_apply (n : ℕ) (z v : ℂ) :
    fderiv ℝ (puncturedCutoff n) z v =
      outerCutoff (n + 1 : ℝ) z * fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z v +
      logarithmicInnerCutoff (n + 1 : ℝ) z * fderiv ℝ (outerCutoff (n + 1 : ℝ)) z v := by
  have hi := (contDiff_logarithmicInnerCutoff (t := (n + 1 : ℝ)) (by positivity)).differentiable (by norm_num) z
  have ho := (contDiff_outerCutoff (n + 1 : ℝ)).differentiable (by norm_num) z
  change fderiv ℝ (fun z => logarithmicInnerCutoff (n + 1 : ℝ) z * outerCutoff (n + 1 : ℝ) z) z v = _
  rw [fderiv_fun_mul hi ho]
  simp
  ring
theorem puncturedCutoff_gradient_energy_eq (n : ℕ) (z : ℂ) :
    ((fderiv ℝ (puncturedCutoff n) z 1) ^ 2 + (fderiv ℝ (puncturedCutoff n) z Complex.I) ^ 2) =
    ((fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
      (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2) +
    ((fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
      (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2) := by
  by_cases hz : ‖z‖ < 1
  · have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have ho : outerCutoff (n + 1 : ℝ) z = 1 := outerCutoff_eq_one (by positivity) (hz.le.trans hn)
    have hd := fderiv_outerCutoff_eq_zero_of_inner (R := (n + 1 : ℝ)) (by positivity) (hz.trans_le hn)
    simp [fderiv_puncturedCutoff_apply, ho, hd]
  · have hz' : 1 ≤ ‖z‖ := le_of_not_gt hz
    have he : Real.exp (-((n : ℝ) + 1)) < 1 := by
      have he' := Real.exp_lt_exp.mpr (show -((n : ℝ) + 1) < 0 by
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith)
      simpa only [Real.exp_zero] using he'
    have hi : logarithmicInnerCutoff (n + 1 : ℝ) z = 1 :=
      logarithmicInnerCutoff_eq_one (by positivity) (he.le.trans hz')
    have hd := fderiv_logarithmicInnerCutoff_eq_zero_of_outer (t := (n + 1 : ℝ)) (by positivity) (he.trans_le hz')
    simp [fderiv_puncturedCutoff_apply, hi, hd]
theorem tendsto_integral_weighted_puncturedCutoff_gradient (u : ℂ → ℝ) (hu : Continuous u)
    (hvanish : Tendsto u (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ z : ℂ, (u z) ^ 2 *
      ((fderiv ℝ (puncturedCutoff n) z 1) ^ 2 +
        (fderiv ℝ (puncturedCutoff n) z Complex.I) ^ 2)) atTop (𝓝 0) := by
  have hi := tendsto_integral_weighted_logarithmicInnerCutoff_gradient u hu
  have ho := tendsto_integral_weighted_outerCutoff_gradient u hu hvanish
  have heq (n : ℕ) : (∫ z : ℂ, (u z) ^ 2 *
      ((fderiv ℝ (puncturedCutoff n) z 1) ^ 2 +
        (fderiv ℝ (puncturedCutoff n) z Complex.I) ^ 2)) =
      (∫ z : ℂ, (u z) ^ 2 * ((fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2)) +
      ∫ z : ℂ, (u z) ^ 2 * ((fderiv ℝ (outerCutoff (n + 1 : ℝ)) z 1) ^ 2 +
        (fderiv ℝ (outerCutoff (n + 1 : ℝ)) z Complex.I) ^ 2) := by
    rw [← integral_add (integrable_weighted_logarithmicInnerCutoff_gradient u hu (by positivity))
      (integrable_weighted_outerCutoff_gradient u hu (by positivity))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [puncturedCutoff_gradient_energy_eq]
    ring
  have hlim := hi.add ho
  simp only [zero_add] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
/-- The cutoff-gradient energy vanishes for a mean-zero logarithmic potential. -/
theorem tendsto_integral_planarLogPotential_puncturedCutoff_gradient {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : ∫ z, φ z = 0) :
    Tendsto (fun n : ℕ => ∫ z : ℂ, (planarLogPotential φ z) ^ 2 *
      ((fderiv ℝ (puncturedCutoff n) z 1) ^ 2 +
       (fderiv ℝ (puncturedCutoff n) z Complex.I) ^ 2)) atTop (𝓝 0) :=
  tendsto_integral_weighted_puncturedCutoff_gradient _
    (contDiff_planarLogPotential hφ).continuous
    (tendsto_planarLogPotential_cocompact hφ.1.continuous hφ.2.1 hφzero)
end HarmonicBalls

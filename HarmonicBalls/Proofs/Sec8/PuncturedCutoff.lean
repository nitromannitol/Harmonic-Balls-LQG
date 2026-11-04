import HarmonicBalls.Proofs.Sec8.WeightedOuterCutoffEnergy

/-! # Smooth compact cutoffs around the puncture

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real ContDiff
namespace HarmonicBalls

/-- Product of the inner and outer cutoffs at a common scale. -/
noncomputable def puncturedCutoff (n : ℕ) (z : ℂ) : ℝ :=
  logarithmicInnerCutoff (n + 1 : ℝ) z * outerCutoff (n + 1 : ℝ) z

theorem contDiff_puncturedCutoff (n : ℕ) : ContDiff ℝ ∞ (puncturedCutoff n) :=
  (contDiff_logarithmicInnerCutoff (by positivity)).mul (contDiff_outerCutoff _)

theorem hasCompactSupport_puncturedCutoff (n : ℕ) : HasCompactSupport (puncturedCutoff n) :=
  (hasCompactSupport_outerCutoff (R := (n + 1 : ℝ)) (by positivity)).mul_left

theorem puncturedCutoff_mem_Icc (n : ℕ) (z : ℂ) : puncturedCutoff n z ∈ Icc (0 : ℝ) 1 := by
  have h1 := logarithmicInnerCutoff_mem_Icc (n + 1 : ℝ) z
  have h2 := outerCutoff_mem_Icc (n + 1 : ℝ) z
  refine ⟨mul_nonneg h1.1 h2.1, ?_⟩
  simpa [puncturedCutoff] using mul_le_mul h1.2 h2.2 h2.1 (show (0 : ℝ) ≤ 1 by norm_num)

theorem puncturedCutoff_eq_zero_near_zero (n : ℕ) : ∃ m : ℕ,
    ∀ z ∈ ball (0 : ℂ) (((m : ℝ) + 1)⁻¹), puncturedCutoff n z = 0 := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (Real.exp_pos (-2 * (n + 1 : ℝ)))
  refine ⟨m, fun z hz => ?_⟩
  have hz' : ‖z‖ ≤ Real.exp (-2 * (n + 1 : ℝ)) := by
    have := (show ‖z‖ < ((m : ℝ) + 1)⁻¹ by simpa [mem_ball, dist_zero_right] using hz)
    exact le_of_lt (this.trans (by simpa [one_div] using hm))
  simp [puncturedCutoff, logarithmicInnerCutoff_eq_zero (by positivity) hz']

theorem ae_tendsto_puncturedCutoff_one :
    ∀ᵐ z : ℂ ∂volume, Tendsto (fun n : ℕ => puncturedCutoff n z) atTop (𝓝 1) := by
  filter_upwards [ae_ne_complex (0 : ℂ)] with z hz
  have h1 := eventually_logarithmicInnerCutoff_eq_one hz
  have h2 := eventually_outerCutoff_eq_one z
  have heq : (fun n : ℕ => puncturedCutoff n z) =ᶠ[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    filter_upwards [h1, h2] with n hn1 hn2
    simp [puncturedCutoff, hn1, hn2]
  exact tendsto_const_nhds.congr' heq.symm

theorem tendsto_integral_mul_puncturedCutoff_pow {f : ℂ → ℝ} (hf : Integrable f) (m : ℕ) :
    Tendsto (fun n : ℕ => ∫ z, f z * puncturedCutoff n z ^ m) atTop (𝓝 (∫ z, f z)) := by
  have hm : ∀ n : ℕ, AEStronglyMeasurable (fun z => f z * puncturedCutoff n z ^ m) volume := by
    intro n
    exact hf.aestronglyMeasurable.mul (((contDiff_puncturedCutoff n).continuous.pow m).aestronglyMeasurable)
  have hb : ∀ n : ℕ, ∀ᵐ z : ℂ ∂volume, ‖f z * puncturedCutoff n z ^ m‖ ≤ ‖f z‖ := by
    intro n
    filter_upwards with z
    have hz := puncturedCutoff_mem_Icc n z
    have hp0 : 0 ≤ puncturedCutoff n z ^ m := pow_nonneg hz.1 _
    have hp1 : puncturedCutoff n z ^ m ≤ 1 := pow_le_one₀ hz.1 hz.2
    rw [norm_mul]
    simp only [Real.norm_eq_abs, abs_of_nonneg hp0]
    exact mul_le_of_le_one_right (abs_nonneg _) hp1
  have hlim : ∀ᵐ z : ℂ ∂volume,
      Tendsto (fun n : ℕ => f z * puncturedCutoff n z ^ m) atTop (𝓝 (f z)) := by
    filter_upwards [ae_tendsto_puncturedCutoff_one] with z hz
    simpa only [one_pow, mul_one] using (tendsto_const_nhds.mul (hz.pow m))
  exact tendsto_integral_of_dominated_convergence (fun z => ‖f z‖) hm hf.norm hb hlim
end HarmonicBalls

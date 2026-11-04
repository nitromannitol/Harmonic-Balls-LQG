import HarmonicBalls.Proofs.Sec8.VagueMassConvergence

/-! # Circle averages of continuous perturbations

A continuous perturbation is recovered locally uniformly from its circle
averages as the radius tends to zero. This is a step towards deriving Weyl
scaling of the LQG measure from its vague-limit definition.
-/

namespace HarmonicBalls.Section6

open Filter Set MeasureTheory
open scoped Topology ENNReal

/-- Circle averages of a continuous function are jointly continuous in
radius and centre, including at radius zero. -/
theorem continuous_circleAverage_radius_center {f : ℂ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1) := by
  simp only [Real.circleAverage_def]
  change Continuous ((2 * Real.pi)⁻¹ • fun p : ℝ × ℂ =>
    ∫ θ in 0..2 * Real.pi, f (circleMap p.2 p.1 θ))
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop [circleMap]

/-- Circle averages converge uniformly on compact sets to the continuous
function as their radii tend to zero. -/
theorem tendstoUniformlyOn_circleAverage {f : ℂ → ℝ} (hf : Continuous f)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun r z => Real.circleAverage f z r) f (𝓝 0) K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1) :=
    continuous_circleAverage_radius_center hf
  have hu : UniformContinuousOn (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1)
      (U ×ˢ K) := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn (F := fun r z => Real.circleAverage f z r)
    (mem_of_mem_nhds hU)
  simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero] using ht

/-- The exponential weights in the Weyl-scaled approximations converge
uniformly on compact sets to the corresponding limiting weight. -/
theorem tendstoUniformlyOn_exp_circleAverage {f : ℂ → ℝ} (hf : Continuous f)
    (γ : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun r z => Real.exp (γ * Real.circleAverage f z r))
      (fun z => Real.exp (γ * f z)) (𝓝 0) K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun p : ℝ × ℂ => Real.exp (γ * Real.circleAverage f p.2 p.1)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_circleAverage_radius_center hf))
  have hu : UniformContinuousOn
      (fun p : ℝ × ℂ => Real.exp (γ * Real.circleAverage f p.2 p.1)) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun r z => Real.exp (γ * Real.circleAverage f z r)) (mem_of_mem_nhds hU)
  simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero] using ht

/-- Vague convergence gives an eventual real bound on the masses of a fixed
compact set. This bound controls errors of uniformly convergent test functions. -/
theorem eventually_measureReal_compact_le_of_vague
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, (ν n).real K ≤ μ.real K + 1 := by
  have hm : μ K ≠ ∞ := hK.measure_ne_top
  have hlim := limsup_measure_compact_le_of_tendsto_compactlySupported ν μ h hK
  have hlt : limsup (fun n => ν n K) atTop < ENNReal.ofReal (μ.real K + 1) := by
    apply lt_of_le_of_lt hlim
    rw [← ENNReal.ofReal_toReal hm]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < μ.real K + 1)).2
      (by simp only [measureReal_def]; linarith)
  filter_upwards [eventually_lt_of_limsup_lt hlt] with n hn
  have hr := ENNReal.toReal_mono (by simp) hn.le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ μ.real K + 1)] at hr
  simpa only [measureReal_def] using hr

end HarmonicBalls.Section6

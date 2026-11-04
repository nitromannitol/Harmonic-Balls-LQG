import HarmonicBalls.Proofs.Sec6.VagueUniformTests
import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder
import HarmonicBalls.Proposed.LQG

/-! # Weyl scaling from the vague-limit definition -/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The regularized measure of a perturbed field is the original regularized
measure weighted by the exponential of the perturbation's circle average. -/
theorem lqgApprox_addCircleAverage (γ r : ℝ) (hr : 0 ≤ r)
    (hε : ℝ → ℂ → ℝ) (hh : Continuous (hε r))
    (f : ℂ → ℝ) (hf : Continuous f) :
    lqgApprox γ (addCircleAverage hε f) r =
      (lqgApprox γ hε r).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * Real.circleAverage f z r))) := by
  have hav : Continuous (fun z => Real.circleAverage f z r) :=
    (continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id)
  have ha : Measurable (fun z => ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * hε r z))) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hh))).measurable
  have hb : Measurable (fun z => ENNReal.ofReal (Real.exp (γ * Real.circleAverage f z r))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hav)).measurable
  simp only [lqgApprox]
  rw [← withDensity_mul volume ha hb]
  apply withDensity_congr_ae
  filter_upwards [] with z
  simp only [Pi.mul_apply, addCircleAverage]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr _) (Real.exp_nonneg _))]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

/-- Integrating against a continuous positive exponential density amounts to
multiplying the test function by the density. -/
theorem integral_withDensity_exp (μ : Measure ℂ) (γ : ℝ) (f φ : ℂ → ℝ)
    (hf : Continuous f) :
    (∫ z, φ z ∂(μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z)))) =
      ∫ z, φ z * Real.exp (γ * f z) ∂μ := by
  have hm : Measurable (fun z => ENNReal.ofReal (Real.exp (γ * f z))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hf)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm (by filter_upwards [] with z; simp) φ]
  congr 1
  funext z
  simp [Real.exp_nonneg, mul_comm]

/-- Multiplication by a continuous test preserves uniform convergence of the
exponential circle-average weights on compact sets. -/
theorem tendstoUniformlyOn_test_exp_circleAverage (γ : ℝ) (f φ : ℂ → ℝ)
    (hf : Continuous f) (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n z => φ z * Real.exp (γ * Real.circleAverage f z (dyadicScale n)))
      (fun z => φ z * Real.exp (γ * f z)) atTop K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) :=
    (hφ.comp continuous_snd).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_circleAverage_radius_center hf)))
  have hu : UniformContinuousOn
      (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun r z => φ z * Real.exp (γ * Real.circleAverage f z r)) (mem_of_mem_nhds hU)
  have ht' : TendstoUniformlyOn (fun r z => φ z * Real.exp (γ * Real.circleAverage f z r))
      (fun z => φ z * Real.exp (γ * f z)) (𝓝 0) K := by
    simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero] using ht
  rw [Metric.tendstoUniformlyOn_iff] at ht' ⊢
  intro ε hε
  have hscale : Tendsto dyadicScale atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact hscale.eventually (ht' ε hε)

/-- Weyl scaling follows deterministically from vague convergence when the
regularized field has continuous profiles at the dyadic scales. -/
theorem isLQGLimit_addCircleAverage {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hμ : IsLQGLimit γ hε μ) (hh : ∀ n, Continuous (hε (dyadicScale n)))
    (f : ℂ → ℝ) (hf : Continuous f) :
    IsLQGLimit γ (addCircleAverage hε f)
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) := by
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  let ν : ℕ → Measure ℂ := fun n => lqgApprox γ hε (dyadicScale n)
  let : ∀ n, IsLocallyFiniteMeasure (ν n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox_of_continuous γ hε (dyadicScale n) (hh n)
  have hfexp : Continuous (fun z => Real.exp (γ * f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf)
  constructor
  · exact IsLocallyFiniteMeasure.withDensity_ofReal hfexp
  · intro φ hφ hφc
    let K := tsupport φ
    have hK : IsCompact K := hφc
    let g : ℕ → ℂ → ℝ := fun n z => φ z * Real.exp (γ * Real.circleAverage f z (dyadicScale n))
    let g₀ : ℂ → ℝ := fun z => φ z * Real.exp (γ * f z)
    have hg : ∀ n, Integrable (g n) (ν n) := by
      intro n
      have hav : Continuous (fun z => Real.circleAverage f z (dyadicScale n)) :=
        (continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id)
      have hgc : Continuous (g n) := hφ.mul (Real.continuous_exp.comp (continuous_const.mul hav))
      exact hgc.integrable_of_hasCompactSupport hφc.mul_right
    have huni : TendstoUniformlyOn g g₀ atTop K :=
      tendstoUniformlyOn_test_exp_circleAverage γ f φ hf hφ hK
    have hoff : ∀ n z, z ∉ K → g n z = g₀ z := by
      intro n z hz
      have hz' : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [g, g₀, hz']
    have hlim := tendsto_integral_of_uniformOn_compact ν μ hμ.tendsto_integral hK
      (hφ.mul hfexp) hφc.mul_right hg huni hoff
    have heq (n : ℕ) : (∫ z, φ z ∂(lqgApprox γ (addCircleAverage hε f) (dyadicScale n))) =
        ∫ z, g n z ∂(ν n) := by
      rw [lqgApprox_addCircleAverage γ (dyadicScale n) (dyadicScale_pos n).le hε (hh n) f hf]
      exact integral_withDensity_exp (ν n) γ (fun z => Real.circleAverage f z (dyadicScale n)) φ
        ((continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id))
    simp_rw [heq, integral_withDensity_exp μ γ f φ hf]
    exact hlim

/-- The simultaneous Weyl-scaling statement follows from the LQG limit and
continuity of the GFF circle-average profiles. -/
theorem lqgMeasureWeylScaling (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureWeylScaling P γ α₀ hC hcirc := by
  intro hgff _ _ _ μ hμ
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fun z => fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z) :=
    ae_all_iff.mpr (fun n => hgff.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n))
  filter_upwards [hμ, hc] with ω hω hωc
  intro f hf
  exact isLQGLimit_addCircleAverage hω hωc f hf

end HarmonicBalls.Section6

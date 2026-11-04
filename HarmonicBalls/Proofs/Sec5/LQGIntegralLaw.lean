import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder
import HarmonicBalls.Proofs.Sec5.ScalingMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Test-function laws of normalized LQG measures -/

namespace HarmonicBalls

open MeasureTheory Filter Topology ProbabilityTheory

/-- Integrals against a countable family of compactly supported continuous
functions have the same joint law for the original and normalized measures.  The coordinate-change and GFF
affine-invariance inputs are staged assumptions. -/
theorem IsWholePlaneGFF.identDistrib_normalizedPullback_integrals
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {k : ℝ} (hk : 0 < k) {f : ι → ℂ → ℝ} (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    IdentDistrib (fun ω i => ∫ z, f i z ∂(μ ω))
      (fun ω i => ∫ z, f i z ∂(normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω))) P P := by
  let _ := h.isGaussianProcess.isProbabilityMeasure
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  have hint : Measurable (fun (m : Measure ℂ) i => ∫ z, f i z ∂m) := by
    apply Measurable.of_eval
    intro i
    exact ((hf i).stronglyMeasurable.integral_kernel (κ := K)).measurable
  let X : ℕ → Ω → ι → ℝ := fun n ω i =>
    ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n))
  let Y : ℕ → Ω → ι → ℝ := fun n ω i =>
    ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage α₀
      (fun s z => hcirc ω (k * s) (k • z) - hcirc ω k 0)) (dyadicScale n))
  let U : Ω → ι → ℝ := fun ω i => ∫ z, f i z ∂(μ ω)
  let V : Ω → ι → ℝ := fun ω i =>
    ∫ z, f i z ∂(normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω))
  have hd (n : ℕ) : IdentDistrib (X n) (Y n) P P := by
    simpa only [Function.comp_def, X, Y] using
      ((h.identDistrib_normalizedScale_lqgApproxSequence hAff γ α₀ hk).comp
        (measurable_pi_apply n)).comp hint
  have hx : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (U ω)) := by
    filter_upwards [hμ] with ω hω
    apply tendsto_pi_nhds.mpr
    intro i
    exact hω.tendsto_integral (f i) (hf i) (hfc i)
  have hy : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (V ω)) := by
    filter_upwards [isLQGMeasureOfField_normalizedPullback hCC h hγ hγ2 hα hμ hk] with ω hω
    apply tendsto_pi_nhds.mpr
    intro i
    exact hω.tendsto_integral (f i) (hf i) (hfc i)
  have hu : AEMeasurable U P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hd n).aemeasurable_fst) hx
  have hv : AEMeasurable V P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hd n).aemeasurable_snd) hy
  have hxu := tendstoInDistribution_of_ae_tendsto (fun n => (hd n).aemeasurable_fst) hu hx
  have hyv := tendstoInDistribution_of_ae_tendsto (fun n => (hd n).aemeasurable_snd) hv hy
  have hxv : TendstoInDistribution X atTop V (fun _ => P) P := by
    refine ⟨fun n => (hd n).aemeasurable_fst, hv, ?_⟩
    convert! hyv.tendsto using 1
    congr 1
    funext n
    apply Subtype.ext
    exact (hd n).map_eq
  exact ⟨hu, hv, tendstoInDistribution_unique X hxu hxv⟩

/-- Integrals of compactly supported continuous functions against the original
and normalized LQG measures have the same law.  The coordinate-change and GFF
affine-invariance inputs are staged assumptions. -/
theorem IsWholePlaneGFF.identDistrib_normalizedPullback_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {k : ℝ} (hk : 0 < k) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    IdentDistrib (fun ω => ∫ z, f z ∂(μ ω))
      (fun ω => ∫ z, f z ∂(normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω))) P P := by
  have hd := h.identDistrib_normalizedPullback_integrals hAff hCC hγ hγ2 hα hμ hk
    (ι := Unit) (f := fun _ => f) (fun _ => hf) (fun _ => hfc)
  simpa only [Function.comp_def] using hd.comp (measurable_pi_apply ())

end HarmonicBalls

import HarmonicBalls.Proofs.Sec8.LQGUniversalApproximationLaw
import HarmonicBalls.Proofs.Sec5.LQGIntegralLaw

/-! # Universality of LQG integrals -/

open MeasureTheory Filter Topology ProbabilityTheory

namespace HarmonicBalls

/-- Compactly supported test integrals of LQG measures have the same joint law
for any two realizations of the same whole-plane field parameters. -/
theorem IsWholePlaneGFF.identDistrib_lqg_integrals_across_spaces
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Countable ι]
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    {f : ι → ℂ → ℝ} (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    IdentDistrib (fun ω i => ∫ z, f i z ∂(μ ω))
      (fun ω i => ∫ z, f i z ∂(μ' ω)) P P' := by
  let _ := h.isProbabilityMeasure
  let _ := h'.isProbabilityMeasure
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  have hint : Measurable (fun (m : Measure ℂ) i => ∫ z, f i z ∂m) := by
    apply Measurable.of_eval
    intro i
    exact ((hf i).stronglyMeasurable.integral_kernel (κ := K)).measurable
  let X : ℕ → Ω → ι → ℝ := fun n ω i =>
    ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n))
  let Y : ℕ → Ω' → ι → ℝ := fun n ω i =>
    ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc' ω)) (dyadicScale n))
  let U : Ω → ι → ℝ := fun ω i => ∫ z, f i z ∂(μ ω)
  let V : Ω' → ι → ℝ := fun ω i => ∫ z, f i z ∂(μ' ω)
  have hd (n : ℕ) : IdentDistrib (X n) (Y n) P P' := by
    simpa only [Function.comp_def, X, Y] using
      ((h.identDistrib_lqgApproxSequence_across_spaces h' γ α₀).comp
        (measurable_pi_apply n)).comp hint
  have hx : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (U ω)) := by
    filter_upwards [hμ] with ω hω
    apply tendsto_pi_nhds.mpr
    intro i
    exact hω.tendsto_integral (f i) (hf i) (hfc i)
  have hy : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (V ω)) := by
    filter_upwards [hμ'] with ω hω
    apply tendsto_pi_nhds.mpr
    intro i
    exact hω.tendsto_integral (f i) (hf i) (hfc i)
  have hu : AEMeasurable U P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hd n).aemeasurable_fst) hx
  have hv : AEMeasurable V P' :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hd n).aemeasurable_snd) hy
  have hxu := tendstoInDistribution_of_ae_tendsto (fun n => (hd n).aemeasurable_fst) hu hx
  have hyv := tendstoInDistribution_of_ae_tendsto (fun n => (hd n).aemeasurable_snd) hv hy
  have hxv : TendstoInDistribution X atTop V (fun _ => P) P' := by
    refine ⟨fun n => (hd n).aemeasurable_fst, hv, ?_⟩
    convert! hyv.tendsto using 1
    congr 1
    funext n
    apply Subtype.ext
    exact (hd n).map_eq
  exact ⟨hu, hv, tendstoInDistribution_unique X hxu hxv⟩

end HarmonicBalls

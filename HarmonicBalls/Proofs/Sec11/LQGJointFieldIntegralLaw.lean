import HarmonicBalls.Proofs.Sec8.LQGUniversalIntegralLaw

/-! # Joint laws of LQG integrals and field observables -/

namespace HarmonicBalls

open MeasureTheory Filter Topology ProbabilityTheory

/-- The LQG measure and any common measurable countable field observable
have the same joint test-integral law for two whole-plane GFF realizations.
The measure is recovered through its circle-average approximations. -/
theorem IsWholePlaneGFF.identDistrib_lqg_integrals_with_observable
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Countable ι]
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    {f : ι → ℂ → ℝ} (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (F : (GFFObservable.Admissible → ℝ) → ℕ → ℝ) (hF : Measurable F) :
    IdentDistrib
      (fun ω => ((fun i => ∫ z, f i z ∂(μ ω)),
        F (fun o => o.1.eval (hC ω) (hcirc ω))))
      (fun ω => ((fun i => ∫ z, f i z ∂(μ' ω)),
        F (fun o => o.1.eval (hC' ω) (hcirc' ω)))) P P' := by
  let _ := h.isProbabilityMeasure
  let _ := h'.isProbabilityMeasure
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  have hint : Measurable (fun (m : Measure ℂ) i => ∫ z, f i z ∂m) := by
    apply Measurable.of_eval
    intro i
    exact ((hf i).stronglyMeasurable.integral_kernel (κ := K)).measurable
  choose A hA hAeq using fun n : ℕ => exists_measurable_lqgApprox_decoder γ (dyadicScale n)
  let circle (n : ℕ) (z : ℂ) : GFFObservable.Admissible :=
    ⟨.circle (dyadicScale n) z, dyadicScale_pos n⟩
  let profile (n : ℕ) (v : GFFObservable.Admissible → ℝ) (z : ℂ) : ℝ :=
    v (circle n z) - α₀ * Real.log (max (dyadicScale n) ‖z‖)
  have hprofile (n : ℕ) : Measurable (profile n) := by
    apply Measurable.of_eval
    intro z
    exact (measurable_pi_apply (circle n z)).sub measurable_const
  let O : Ω → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC ω) (hcirc ω)
  let O' : Ω' → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC' ω) (hcirc' ω)
  let X : ℕ → Ω → (ι → ℝ) × (ℕ → ℝ) := fun n ω =>
    (fun i => ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n)), F (O ω))
  let Y : ℕ → Ω' → (ι → ℝ) × (ℕ → ℝ) := fun n ω =>
    (fun i => ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc' ω)) (dyadicScale n)), F (O' ω))
  let U : Ω → (ι → ℝ) × (ℕ → ℝ) := fun ω =>
    (fun i => ∫ z, f i z ∂(μ ω), F (O ω))
  let V : Ω' → (ι → ℝ) × (ℕ → ℝ) := fun ω =>
    (fun i => ∫ z, f i z ∂(μ' ω), F (O' ω))
  have hd (n : ℕ) : IdentDistrib (X n) (Y n) P P' := by
    let decode : (GFFObservable.Admissible → ℝ) → (ι → ℝ) × (ℕ → ℝ) :=
      fun v => ((fun i => ∫ z, f i z ∂(A n (profile n v))), F v)
    have hdecode : Measurable decode := ((hint.comp ((hA n).comp (hprofile n))).prodMk hF)
    have hlaw := (h.identDistrib_observables_across_spaces h').comp hdecode
    have heq : ∀ᵐ ω ∂P, decode (O ω) = X n ω := by
      filter_upwards [h.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)] with ω hω
      have hp : profile n (O ω) = fun z => fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z := by
        funext z
        exact (fieldCircleAverage_eq α₀ _ (dyadicScale_pos n) z).symm
      simp only [decode, X, hp, hAeq n _ hω, lqgApprox]
    have heq' : ∀ᵐ ω ∂P', decode (O' ω) = Y n ω := by
      filter_upwards [h'.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)] with ω hω
      have hp : profile n (O' ω) = fun z => fieldCircleAverage α₀ (hcirc' ω) (dyadicScale n) z := by
        funext z
        exact (fieldCircleAverage_eq α₀ _ (dyadicScale_pos n) z).symm
      simp only [decode, Y, hp, hAeq n _ hω, lqgApprox]
    exact ((IdentDistrib.of_ae_eq hlaw.aemeasurable_fst heq).symm.trans hlaw).trans
      (IdentDistrib.of_ae_eq hlaw.aemeasurable_snd heq')
  have hx : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (U ω)) := by
    filter_upwards [hμ] with ω hω
    apply Tendsto.prodMk_nhds
    · apply tendsto_pi_nhds.mpr
      intro i
      exact hω.tendsto_integral (f i) (hf i) (hfc i)
    · exact tendsto_const_nhds
  have hy : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (V ω)) := by
    filter_upwards [hμ'] with ω hω
    apply Tendsto.prodMk_nhds
    · apply tendsto_pi_nhds.mpr
      intro i
      exact hω.tendsto_integral (f i) (hf i) (hfc i)
    · exact tendsto_const_nhds
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

#print axioms IsWholePlaneGFF.identDistrib_lqg_integrals_with_observable

end HarmonicBalls

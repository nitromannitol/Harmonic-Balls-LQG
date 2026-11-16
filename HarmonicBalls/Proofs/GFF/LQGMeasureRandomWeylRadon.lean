import HarmonicBalls.Proofs.GFF.LQGMeasureRandomWeylMeasurability
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds

/-!
# The LQG measure reweighted by a random continuous function is a non-atomic Radon measure

Let `h = h^ℂ - α log |·|`, where `h^ℂ` is a whole-plane GFF, `0 < γ < 2` and `α < Q`, and let
`μ_h` be the γ-LQG measure of `h`. For a random continuous function `F` (`F ω` is continuous for
every `ω` and `ω ↦ F ω z` is measurable for every `z`), the measure `μ_{h+F} = e^{γ F} μ_h`
(Fact 2.1 III, with `f` random continuous as allowed at line 406) satisfies Fact 2.1 I: almost
surely it is a non-atomic Radon measure.

The argument is the one the paper calls immediate from the construction. Almost surely `μ_h` is
locally finite (part of `IsLQGMeasureOfField`) and has no atoms (`lqgMeasureNonatomic_holds`).
Multiplying by the continuous density `e^{γ F ω}` preserves both properties: the density is bounded
on a neighbourhood of every point, and the reweighted measure is absolutely continuous with respect
to `μ_h`. On `ℂ` every locally finite measure is regular and inner regular.

The almost sure event depends only on the field. On it the conclusions hold for every continuous
function at once, together with the vague convergence of the circle-average approximations of
`h + f` to `e^{γ f} μ_h` (`ae_tendsto_integral_lqgApprox_continuum_add_continuous`). For a random
continuous `F` the reweighted random measure is moreover almost everywhere measurable
(`IsWholePlaneGFF.aemeasurable_withDensity_exp_lqgMeasure`).
-/

open MeasureTheory Filter Topology

namespace HarmonicBalls

/-- The reweighting `e^{γ f} μ` of a locally finite measure `μ` on `ℂ` without atoms by a continuous
function `f` is a locally finite, regular and inner regular measure without atoms. -/
theorem nullSingletonClass_isLocallyFiniteMeasure_withDensity_exp {μ : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] (γ : ℝ) {f : ℂ → ℝ} (hf : Continuous f) :
    NullSingletonClass (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) ∧
      IsLocallyFiniteMeasure (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) ∧
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))).Regular ∧
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))).InnerRegular := by
  have hlf : IsLocallyFiniteMeasure (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal (Real.continuous_exp.comp (continuous_const.mul hf))
  exact ⟨⟨fun z => withDensity_absolutelyContinuous μ _ (measure_singleton z)⟩, hlf, inferInstance,
    inferInstance⟩

/-- **Fact 2.1 I for `μ_{h+f}`, on one event of the field.** Let `h = h^ℂ - α log |·|` be a
whole-plane field with `0 < γ < 2` and `α < Q`, and let `μ` be its LQG measure. Almost surely, for
every continuous `f : ℂ → ℝ`, the measure `e^{γ f} μ_h` is a locally finite, regular and inner
regular measure without atoms, and it is the vague limit of the circle-average approximations of
`h + f` as the radius tends to `0`. -/
theorem IsWholePlaneGFF.ae_forall_nullSingletonClass_withDensity_exp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      NullSingletonClass ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) ∧
      IsLocallyFiniteMeasure ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) ∧
      ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))).Regular ∧
      ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))).InnerRegular ∧
      ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
        Tendsto (fun s : ℝ =>
            ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) f) s))
          (𝓝[>] 0)
          (𝓝 (∫ z, φ z ∂((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))))) := by
  have hlim : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hna : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0 :=
    lqgMeasureNonatomic_holds Ω P γ α hC hcirc hh hγ0 hγ2 hαQ μ hμ
  filter_upwards [hlim, hna,
    ae_tendsto_integral_lqgApprox_continuum_add_continuous hh hγ0 hγ2 hαQ hμ]
    with ω hω hωna hωconv f hf
  have : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
  have : NullSingletonClass (μ ω) := ⟨hωna⟩
  obtain ⟨h1, h2, h3, h4⟩ :=
    nullSingletonClass_isLocallyFiniteMeasure_withDensity_exp (μ := μ ω) γ hf
  exact ⟨h1, h2, h3, h4, hωconv f hf⟩

/-- **Fact 2.1 I for the LQG measure reweighted by a random continuous function.** Let
`h = h^ℂ - α log |·|` be a whole-plane field with `0 < γ < 2` and `α < Q`, let `μ` be its LQG
measure, and let `F` be a random continuous function: `F ω` is continuous for every `ω` and
`ω ↦ F ω z` is measurable for every `z`. Then the random measure `μ_{h+F} = e^{γ F} μ_h` is almost
everywhere measurable, and almost surely it is a locally finite, regular and inner regular measure
without atoms which is the vague limit of the circle-average approximations of `h + F` as the radius
tends to `0`. -/
theorem IsWholePlaneGFF.aemeasurable_and_ae_nullSingletonClass_withDensity_exp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {F : Ω → ℂ → ℝ} (hFc : ∀ ω, Continuous (F ω)) (hFm : ∀ z, Measurable fun ω => F ω z) :
    AEMeasurable (fun ω => (μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))) P ∧
      ∀ᵐ ω ∂P,
        NullSingletonClass ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))) ∧
        IsLocallyFiniteMeasure ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))) ∧
        ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))).Regular ∧
        ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))).InnerRegular ∧
        ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
          Tendsto (fun s : ℝ =>
              ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) (F ω)) s))
            (𝓝[>] 0)
            (𝓝 (∫ z, φ z ∂((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))))) := by
  refine ⟨hh.aemeasurable_withDensity_exp_lqgMeasure hμ hFc hFm, ?_⟩
  filter_upwards [hh.ae_forall_nullSingletonClass_withDensity_exp hγ0 hγ2 hαQ hμ] with ω hω
  exact hω (F ω) (hFc ω)

end HarmonicBalls

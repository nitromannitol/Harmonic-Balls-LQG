import HarmonicBalls.Proofs.Potential.LQGSmoothDomainGreenHolder
import HarmonicBalls.Proofs.Potential.SigmaFiniteDensityGreenLaplacian
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity

/-! # Distributional equation for singular LQG Green potentials -/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Filter
open scoped ENNReal NNReal

/-- On one event, every bounded-density Green potential on every smooth bounded
open set has the stated pointwise integrability, Hölder regularity, and
its distributional Laplacian is the negative of its weighted source. -/
theorem IsWholePlaneGFF.ae_singular_greenPotential_smooth_poisson
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (O : Set ℂ), IsSmoothBoundedOpen O → ∀ f : ℂ → ℝ,
      MemLp f ⊤ ((μ ω).restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O (μ ω)) ∧
      (∃ C r : ℝ≥0, 0 < r ∧ HolderOnWith C r
        (fun x => ∫ y in O, greenFunction O x y * f y ∂(μ ω)) (closure O)) ∧
      ∀ φ : ℂ → ℝ, IsTestFunction O φ →
        (∫ x, (∫ y in O, greenFunction O x y * f y ∂(μ ω)) * Δ φ x) =
          -(∫ y in O, f y * φ y ∂(μ ω)) := by
  filter_upwards [hh.ae_singular_greenPotential_smooth_holder hγ hγ2 hαQ hμ, hμ] with ω hhld hlim
  let := hlim.isLocallyFiniteMeasure
  intro O hO f hf
  obtain ⟨hint, hholder⟩ := hhld O hO f hf
  refine ⟨hint, hholder, ?_⟩
  intro φ hφ
  have hOo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  obtain ⟨R, hR⟩ := hO.1.subset_ball (0 : ℂ)
  let : IsFiniteMeasure ((μ ω).restrict O) := GreenGeneral.isFiniteMeasure_restrict_of_subset_ball hR
  have hfO : MemLp f ⊤ ((μ ω).restrict O) :=
    hf.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  let g := hfO.aestronglyMeasurable.mk f
  have hg : Measurable g := hfO.aestronglyMeasurable.measurable_mk
  have hfg : f =ᵐ[((μ ω).restrict O)] g := hfO.aestronglyMeasurable.ae_eq_mk
  have hgi : Integrable g ((μ ω).restrict O) := (hfO.integrable (by simp)).congr hfg
  have hν : ∀ᵐ y ∂((μ ω).restrict O), y ∈ O := ae_restrict_mem hOo.measurableSet
  have hp := hasLaplacian_sigmaFinite_density_transposedGreen hOo hO.1 hν hg hgi
  obtain ⟨B, hB⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have heq := ((hp.2.2.2 φ hφ).2.2).trans
    (integral_negativeSource_sub_positiveSource hg hgi hφ.1.continuous.measurable
      (Filter.Eventually.of_forall hB))
  have hpot (x : ℂ) : (∫ y, g y * greenFunction O y x ∂((μ ω).restrict O)) =
      ∫ y in O, greenFunction O x y * f y ∂(μ ω) := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy, greenFunction_bounded_open_comm hOo hO.1 y x, mul_comm]
  simp_rw [hpot] at heq
  rw [heq]
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

end HarmonicBalls

import HarmonicBalls.Proofs.Sec8.GermConditionalKernel
import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-! # Normalized LQG measure from the ordinary local field -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- A finite positive change of mass normalization leaves the normalized
restriction unchanged, including for measures with infinite total mass. -/
theorem normalizedRestriction_smul (μ : Measure ℂ) (U : Set ℂ) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ∞) :
    normalizedRestriction (c • μ) U = normalizedRestriction μ U := by
  apply Measure.ext
  intro A hA
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA]
  rw [← ENNReal.div_eq_inv_mul, ← ENNReal.div_eq_inv_mul]
  exact ENNReal.mul_div_mul_left _ _ hc hct

/-- Normalization depends only on the restriction to the reference set. -/
theorem normalizedRestriction_restrict (μ : Measure ℂ) {U : Set ℂ}
    (hU : MeasurableSet U) :
    normalizedRestriction (μ.restrict U) U = normalizedRestriction μ U := by
  simp only [normalizedRestriction, Measure.restrict_apply hU, inter_self,
    Measure.restrict_restrict hU]

/-- Locally proportional measures have the same normalized restriction. -/
theorem normalizedRestriction_eq_of_restrict_eq_smul {μ ν : Measure ℂ} {U : Set ℂ}
    (hU : MeasurableSet U) {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞)
    (h : ν.restrict U = c • μ.restrict U) :
    normalizedRestriction ν U = normalizedRestriction μ U := by
  rw [← normalizedRestriction_restrict ν hU, h, normalizedRestriction_smul _ U hc hct,
    normalizedRestriction_restrict μ hU]

/-- A density that is constant and positive on the reference set leaves the
normalized restriction unchanged. In particular, this is the local algebra
needed for Weyl shifts that are constant on the reference set. -/
theorem normalizedRestriction_withDensity_of_eq_const (μ : Measure ℂ) {U : Set ℂ}
    (hU : MeasurableSet U) (f : ℂ → ℝ≥0∞) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ∞) (hf : ∀ x ∈ U, f x = c) :
    normalizedRestriction (μ.withDensity f) U = normalizedRestriction μ U := by
  apply normalizedRestriction_eq_of_restrict_eq_smul hU hc hct
  rw [restrict_withDensity hU]
  have heq : f =ᵐ[μ.restrict U] (fun _ => c) :=
    (ae_restrict_mem hU).mono fun x hx => hf x hx
  rw [withDensity_congr_ae heq, withDensity_const]

/-- A Weyl density from a function constant on the reference set leaves the
normalized restriction unchanged. -/
theorem normalizedRestriction_weyl_of_eq_const (μ : Measure ℂ) {U : Set ℂ}
    (hU : MeasurableSet U) (γ : ℝ) (f : ℂ → ℝ) (a : ℝ)
    (hf : ∀ x ∈ U, f x = a) :
    normalizedRestriction (μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) U =
      normalizedRestriction μ U := by
  apply normalizedRestriction_withDensity_of_eq_const μ hU _
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top
  intro x hx
  rw [hf x hx]

/-- The normalized mass of a Borel set has an almost-sure version measurable
with respect to the ordinary local field. The staged LQG locality property is
an explicit hypothesis; no claim about the field modulo constants is made. -/
theorem exists_ordinaryField_lqg_ratio_version
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hlocal : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : Set ℂ) (hA : MeasurableSet A) :
    ∃ Y : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ (fieldSigmaAlgebra α₀ hC U) _ Y ∧
      (fun ω => μ ω (A ∩ U) / μ ω U) =ᵐ[P] Y := by
  obtain ⟨Y, hYm, hY⟩ := exists_local_lqg_borel_mass_representative
    hγ hγ2 hα hGFF hμ hlocal hU hUb A hA
  obtain ⟨Z, hZm, hZ⟩ := hlocal hGFF hγ hγ2 hα μ hμ U hU
  refine ⟨fun ω => Y ω / Z ω, hYm.div hZm, ?_⟩
  filter_upwards [hY, hZ] with ω hYω hZω
  rw [hYω, hZω]

/-- If its mass on a bounded open set is positive, the normalized LQG
restriction has an almost-sure version measurable for the ordinary local
field. This isolates the remaining passage to the field modulo constants. -/
theorem exists_ordinaryField_lqg_normalizedRestriction_version
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hlocal : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hpositive : ∀ᵐ ω ∂P, μ ω U ≠ 0) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) (fieldSigmaAlgebra α₀ hC U) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) U := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hposfin : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞ := by
    filter_upwards [hpositive, hμ] with ω hp hlim
    let : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
    obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
    exact ⟨hp, ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hr)⟩
  apply exists_normalizedRestriction_version_of_aemeasurable_ae_open_ratios P
    (fieldSigmaAlgebra α₀ hC U) (hGFF.fieldSigmaAlgebra_le α₀ U)
    μ (hGFF.aemeasurable_lqgMeasure hμ) U hU.measurableSet hposfin
  intro V hV
  exact exists_ordinaryField_lqg_ratio_version hγ hγ2 hα hGFF hμ hlocal hU hUb
    V hV.measurableSet

/-- Under the staged Weyl scaling property, a continuous perturbation that is
constant on a reference set has an LQG limit with the same normalized local
restriction. -/
theorem ae_lqg_weyl_same_normalizedRestriction
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hWeyl : LQGMeasureWeylScaling P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : MeasurableSet U) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ a : ℝ,
      (∀ x ∈ U, f x = a) →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f)
        ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
      normalizedRestriction
        ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) U =
          normalizedRestriction (μ ω) U := by
  filter_upwards [hWeyl hGFF hγ hγ2 hα μ hμ] with ω hω f hf a hfa
  exact ⟨hω f hf, normalizedRestriction_weyl_of_eq_const (μ ω) hU γ f a hfa⟩

end HarmonicBalls

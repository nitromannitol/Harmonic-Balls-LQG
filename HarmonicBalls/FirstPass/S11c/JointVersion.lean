import HarmonicBalls.Defs.LQG
import HarmonicBalls.Steps.Sec11.PinchNormalizedMeasure

/-!
# Proposition 11.7, almost-sure measurability of the scale-event ingredients

Let `M : Ω × ℝ → Measure ℂ` be jointly measurable and such that, almost surely, for every
`α < lqgQ γ`, `M (ω, α)` is the γ-LQG measure of the circle averages `fieldCircleAverage α (hcirc ω)` (the conclusion of
`exists_jointly_measurable_subcritical_lqgMeasures`, `HarmonicBalls/Proofs/Sec6/JointSingularMeasureMeasurability.lean`).
If `μ` is the LQG measure of the field `h = h^ℂ - α₀ log|·|` (`IsLQGMeasureOfField`, `α₀ < lqgQ γ`), then `μ ω = M (ω, α₀)`
almost surely (`IsLQGMeasure.ae_eq`, `Defs/LQG.lean`). Consequently:
* the masses `ω ↦ μ ω B` of Borel sets are almost surely measurable;
* the integrals `ω ↦ ∫⁻ f d(μ ω)` of measurable `f` are almost surely measurable;
* the annular Green-potential supremum `annulusGreenPotentialSup (μ ω) z a b` (`HarmonicBalls/Defs/Annuli.lean:65`) has an
  a.s. measurable version, by the lower-semicontinuity argument of `exists_local_annulusGreenPotentialSup_of_borel_mass`
  (`HarmonicBalls/Steps/Sec11/PinchNormalizedMeasure.lean`, reused).
These are the measurability inputs of the scale events `coneMassEvent` (`HarmonicBalls/Draft/Section11.lean:72`) of Lemma 11.7
(paper `lemma:mu_h-bad-and-harnack`, corrected paper line 2896).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The LQG measure of the field equals the jointly measurable version at insertion `α₀`, almost surely. -/
theorem ae_eq_joint_version {P : Measure Ω} {γ α₀ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {M : Ω × ℝ → Measure ℂ}
    (hMlim : ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)))
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hα₀ : α₀ < lqgQ γ) :
    ∀ᵐ ω ∂P, μ ω = M (ω, α₀) := by
  have hν : IsLQGMeasure P γ (fun ω => fieldCircleAverage α₀ (hcirc ω)) (fun ω => M (ω, α₀)) := by
    filter_upwards [hMlim] with ω hω
    exact hω α₀ hα₀
  exact IsLQGMeasure.ae_eq hμ hν

/-- The masses `μ ω B` of Borel sets are almost surely measurable. -/
theorem aemeasurable_mass_of_joint_version {P : Measure Ω} {γ α₀ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {M : Ω × ℝ → Measure ℂ} (hM : Measurable M)
    (hMlim : ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)))
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hα₀ : α₀ < lqgQ γ) :
    ∀ B : Set ℂ, MeasurableSet B → AEMeasurable (fun ω => μ ω B) P := by
  have heq := ae_eq_joint_version hMlim hμ hα₀
  intro B hB
  have hmeas : Measurable fun ω => M (ω, α₀) B :=
    (Measure.measurable_coe hB).comp (hM.comp (measurable_id.prodMk measurable_const))
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [heq] with ω hω
  show M (ω, α₀) B = μ ω B
  rw [hω]

/-- The integrals `ω ↦ ∫⁻ f d(μ ω)` of a measurable `f : ℂ → ℝ≥0∞` are almost surely measurable. -/
theorem aemeasurable_lintegral_of_joint_version {P : Measure Ω} {γ α₀ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {M : Ω × ℝ → Measure ℂ} (hM : Measurable M)
    (hMlim : ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)))
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hα₀ : α₀ < lqgQ γ)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ y, f y ∂(μ ω)) P := by
  have heq := ae_eq_joint_version hMlim hμ hα₀
  have hmeas : Measurable fun ω => ∫⁻ y, f y ∂(M (ω, α₀)) :=
    (Measure.measurable_lintegral hf).comp (hM.comp (measurable_id.prodMk measurable_const))
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [heq] with ω hω
  show ∫⁻ y, f y ∂(M (ω, α₀)) = ∫⁻ y, f y ∂(μ ω)
  rw [hω]

/-- The annular Green-potential supremum `annulusGreenPotentialSup (μ ω) z a b` has an a.s. measurable version. -/
theorem exists_measurable_annulusGreenPotentialSup_of_joint_version {P : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {M : Ω × ℝ → Measure ℂ} (hM : Measurable M)
    (hMlim : ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)))
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hα₀ : α₀ < lqgQ γ) (z : ℂ) (a b : ℝ) :
    ∃ Y : Ω → ℝ≥0∞, Measurable Y ∧ ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) z a b = Y ω := by
  have heq := ae_eq_joint_version hMlim hμ hα₀
  have hmass : ∀ B : Set ℂ, MeasurableSet B → B ⊆ ball z b →
      ∃ Y : Ω → ℝ≥0∞, Measurable[inferInstance] Y ∧ ∀ᵐ ω ∂P, μ ω B = Y ω := by
    intro B hB _
    refine ⟨fun ω => M (ω, α₀) B, ?_, ?_⟩
    · exact (Measure.measurable_coe hB).comp (hM.comp (measurable_id.prodMk measurable_const))
    · filter_upwards [heq] with ω hω
      show μ ω B = M (ω, α₀) B
      rw [hω]
  obtain ⟨Y, hY, hYeq⟩ :=
    exists_local_annulusGreenPotentialSup_of_borel_mass P inferInstance μ z a b hmass
  exact ⟨Y, hY, hYeq⟩

end HarmonicBalls.S11c

import HarmonicBalls.Defs.LQG

/-!
# Proposition 11.7, almost-sure measurability of the LQG mass functionals (fp-S11c, owner n1)

FIRST-PASS NEW (no new Props). Let `M : Ω × ℝ → Measure ℂ` be jointly measurable and such that, almost surely, for every
`α < lqgQ γ`, `M (ω, α)` is the γ-LQG measure of the circle averages `fieldCircleAverage α (hcirc ω)` (the conclusion of
`exists_jointly_measurable_subcritical_lqgMeasures`, `HarmonicBalls/Proofs/Sec6/JointSingularMeasureMeasurability.lean`).
If `μ` is the LQG measure of the field `h = h^ℂ - α₀ log|·|` (`IsLQGMeasureOfField`, `α₀ < lqgQ γ`), then `μ ω = M (ω, α₀)`
almost surely (`IsLQGMeasure.ae_eq`, `Defs/LQG.lean`). Hence the masses `ω ↦ μ ω B` of Borel sets `B` and the integrals
`ω ↦ ∫⁻ f d(μ ω)` of measurable `f` are almost surely measurable. This is the measurability input of the scale events
`coneMassEvent` (`HarmonicBalls/Draft/Section11.lean:72`) of Lemma 11.7 (paper `lemma:mu_h-bad-and-harnack`, corrected paper
line 2896). The annular supremum `annulusGreenPotentialSup` (`HarmonicBalls/Defs/Annuli.lean:65`) is still open.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls.S11c

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The masses `μ ω B` of Borel sets are almost surely measurable when `μ` is the LQG measure of the field `h^ℂ - α₀ log|·|`
and `M` is a jointly measurable version of the LQG measures at all insertions `α < lqgQ γ`. -/
theorem aemeasurable_mass_of_joint_version {P : Measure Ω} {γ α₀ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {M : Ω × ℝ → Measure ℂ} (hM : Measurable M)
    (hMlim : ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)))
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hα₀ : α₀ < lqgQ γ) :
    ∀ B : Set ℂ, MeasurableSet B → AEMeasurable (fun ω => μ ω B) P := by
  have hν : IsLQGMeasure P γ (fun ω => fieldCircleAverage α₀ (hcirc ω)) (fun ω => M (ω, α₀)) := by
    filter_upwards [hMlim] with ω hω
    exact hω α₀ hα₀
  have heq : ∀ᵐ ω ∂P, μ ω = M (ω, α₀) := IsLQGMeasure.ae_eq hμ hν
  intro B hB
  have hmeas : Measurable fun ω => M (ω, α₀) B :=
    (Measure.measurable_coe hB).comp (hM.comp (measurable_id.prodMk measurable_const))
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [heq] with ω hω
  show M (ω, α₀) B = μ ω B
  rw [hω]

/-- The integrals `ω ↦ ∫⁻ f d(μ ω)` of a measurable `f : ℂ → ℝ≥0∞` are almost surely measurable under the same hypotheses. -/
theorem aemeasurable_lintegral_of_joint_version {P : Measure Ω} {γ α₀ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {M : Ω × ℝ → Measure ℂ} (hM : Measurable M)
    (hMlim : ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)))
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hα₀ : α₀ < lqgQ γ)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ y, f y ∂(μ ω)) P := by
  have hν : IsLQGMeasure P γ (fun ω => fieldCircleAverage α₀ (hcirc ω)) (fun ω => M (ω, α₀)) := by
    filter_upwards [hMlim] with ω hω
    exact hω α₀ hα₀
  have heq : ∀ᵐ ω ∂P, μ ω = M (ω, α₀) := IsLQGMeasure.ae_eq hμ hν
  have hmeas : Measurable fun ω => ∫⁻ y, f y ∂(M (ω, α₀)) :=
    (Measure.measurable_lintegral hf).comp (hM.comp (measurable_id.prodMk measurable_const))
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [heq] with ω hω
  show ∫⁻ y, f y ∂(M (ω, α₀)) = ∫⁻ y, f y ∂(μ ω)
  rw [hω]

end HarmonicBalls.S11c

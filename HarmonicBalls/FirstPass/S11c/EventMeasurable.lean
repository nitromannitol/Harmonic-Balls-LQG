import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Proposition 11.7, measurability of Green-type integrals against a random measure (fp-S11c, owner n1)

FIRST-PASS NEW (generic measure theory, no Props). If `ω ↦ μ ω B` is measurable for every measurable set `B`, then
`ω ↦ ∫⁻ y, f y ∂(μ ω)` is measurable for every measurable `f : α → ℝ≥0∞`. This is the step that turns the measurability
of masses `μ_h(B)` into measurability of the annular potentials `∫ G(x, y) μ_h(dy)` used by the scale events
`coneMassEvent` of Lemma 11.7 (paper `lemma:mu_h-bad-and-harnack`, corrected paper line 2896; the event is defined in
`HarmonicBalls/Draft/Section11.lean:72`).
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- If the masses `ω ↦ μ ω B` are measurable for all measurable `B`, the integrals `ω ↦ ∫⁻ f d(μ ω)` of a measurable
`f : α → ℝ≥0∞` are measurable in `ω`. -/
theorem measurable_lintegral_of_mass {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Ω → Measure α) (hμ : ∀ B : Set α, MeasurableSet B → Measurable fun ω => μ ω B)
    {f : α → ℝ≥0∞} (hf : Measurable f) : Measurable fun ω => ∫⁻ y, f y ∂(μ ω) :=
  (Measure.measurable_lintegral hf).comp (Measure.measurable_of_measurable_coe μ hμ)

end HarmonicBalls.S11c

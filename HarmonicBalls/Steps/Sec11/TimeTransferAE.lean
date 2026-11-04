import HarmonicBalls.Steps.Sec11.FullCompactCover
import HarmonicBalls.Steps.Sec11.TimeTransfer

/-! # Transfer through an almost-everywhere continuous map -/

namespace HarmonicBalls

open MeasureTheory Set Filter

/-- An almost-everywhere continuous measurable map sends any almost-everywhere
pointwise property to almost every image point. No measurability of the target
property is required. -/
theorem ae_map_of_ae_continuousAt
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] [Measure.InnerRegularCompactLTTop μ]
    (f : X → ℝ) (P : ℝ → Prop) (hf : AEMeasurable f μ)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt f x) (hP : ∀ᵐ x ∂μ, P (f x)) :
    ∀ᵐ y ∂(μ.map f), P y := by
  have hgood : ∀ᵐ x ∂μ, ContinuousAt f x ∧ P (f x) := hcont.and hP
  obtain ⟨K, hK, hgoodK, hfull⟩ := exists_compact_full_cover_of_ae μ _ hgood
  apply ae_map_of_countable_compact_full_cover μ f K P hf hK _ hfull
  · intro n x hx
    exact (hgoodK n x hx).2
  · intro n x hx
    exact (hgoodK n x hx).1.continuousWithinAt

end HarmonicBalls

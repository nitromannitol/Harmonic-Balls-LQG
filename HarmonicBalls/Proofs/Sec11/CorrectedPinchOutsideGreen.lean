import HarmonicBalls.Proofs.Sec11.CorrectedPinchCoreGeometry
import HarmonicBalls.Proofs.Sec11.NormalizedPinchData

/-! # Outside locality of the annular Green potential -/

namespace HarmonicBalls
open MeasureTheory Set Metric
open scoped ENNReal

/-- The annulus used for the Green potential lies outside the closed core. -/
theorem IsCorrectedPinchConfiguration.green_annulus_subset_outside
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    annulus 0 3 6 ⊆ (closure W)ᶜ := by
  have hW : closure W ⊆ annulus 0 1 2 := by
    have ht : closure W ⊆ thickening (10 * δ) (closure W) :=
      self_subset_thickening (by have := h.δ₀_mem.1; positivity) _
    exact ht.trans (subset_closure.trans (h.buffer_W.trans inter_subset_right))
  intro x hx hxW
  have hx2 : dist x (0 : ℂ) < 2 := (hW hxW).1
  have hx3 : x ∈ closedBall (0 : ℂ) 3 := by
    rw [mem_closedBall]
    linarith
  exact hx.2 hx3

/-- The Green-potential supremum is determined by the outside restriction. -/
theorem IsCorrectedPinchConfiguration.green_potential_restrict_outside
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (μ : Measure ℂ) :
    annulusGreenPotentialSup (μ.restrict (closure W)ᶜ) 0 3 6 =
      annulusGreenPotentialSup μ 0 3 6 :=
  annulusGreenPotentialSup_restrict μ 0 3 6 _ h.green_annulus_subset_outside

/-- Measurability of the outside measure restriction implies the Green
observable measurability needed in the joint pinch argument. -/
theorem IsCorrectedPinchConfiguration.measurable_green_of_outside_measure
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ) (M : ℝ)
    (hm : Measurable fun ω => (μ ω).restrict (closure W)ᶜ) :
    Measurable fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 := by
  have hg := (measurable_annulusGreenPotentialSup 0 3 6).comp hm
  have hg' : Measurable fun ω => annulusGreenPotentialSup (μ ω) 0 3 6 := by
    convert hg using 1
    ext ω
    exact (h.green_potential_restrict_outside (μ ω)).symm
  exact measurable_const.mul hg'

#print axioms IsCorrectedPinchConfiguration.green_annulus_subset_outside
#print axioms IsCorrectedPinchConfiguration.green_potential_restrict_outside
#print axioms IsCorrectedPinchConfiguration.measurable_green_of_outside_measure
end HarmonicBalls

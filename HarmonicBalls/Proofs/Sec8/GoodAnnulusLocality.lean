import HarmonicBalls.Defs.Annuli

/-! # Locality of the good-annulus condition

The good-annulus event only uses the measure inside the annulus. This is the
measure-theoretic part of the locality needed in the proof of Lemma 8.3.
-/

open MeasureTheory Metric Set

namespace HarmonicBalls

/-- Goodness depends only on the restriction of the measure to the annulus. -/
theorem isGoodAnnulus_congr_of_restrict_eq (μ ν : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ)
    (h : μ.restrict (annulus z (3 * r) (5 * r)) =
      ν.restrict (annulus z (3 * r) (5 * r))) :
    IsGoodAnnulus μ r z a b ↔ IsGoodAnnulus ν r z a b := by
  have hA : MeasurableSet (annulus z (3 * r) (5 * r)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have heq (Y : Set ℂ) (hY : MeasurableSet Y)
      (hYA : Y ⊆ annulus z (3 * r) (5 * r)) : μ Y = ν Y := by
    have := congrArg (fun m : Measure ℂ => m Y) h
    simpa only [Measure.restrict_apply hY, inter_eq_left.mpr hYA] using this
  have hmass := heq _ hA (subset_refl _)
  unfold IsGoodAnnulus
  constructor <;> intro hg Y hY hYA hsmall u hu
  · apply hg Y hY hYA _ u hu
    rwa [heq Y hY hYA, hmass]
  · apply hg Y hY hYA _ u hu
    rwa [← heq Y hY hYA, ← hmass]

/-- Restriction to any region containing the annulus leaves the
good-annulus condition unchanged. -/
theorem isGoodAnnulus_restrict (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ)
    (U : Set ℂ)
    (hAU : annulus z (3 * r) (5 * r) ⊆ U) :
    IsGoodAnnulus (μ.restrict U) r z a b ↔ IsGoodAnnulus μ r z a b := by
  apply isGoodAnnulus_congr_of_restrict_eq
  exact Measure.restrict_restrict_of_subset hAU

end HarmonicBalls

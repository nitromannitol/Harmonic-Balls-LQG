import HarmonicBalls.Proofs.Sec8.GoodEventMeasurablePositive
import HarmonicBalls.Proofs.Sec6.LogAnnulusHitting

/-! # Good-annulus measurability from planar Brownian point polarity -/

open MeasureTheory Metric Set

namespace HarmonicBalls

/-- At a positive mass threshold, the good-annulus event is measurable for
all measures. -/
theorem measurableSet_isGoodAnnulus_of_pos
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b} := by
  apply measurableSet_isGoodAnnulus_of_ae_point_avoidance r hr z a b ha
  intro u _ x _ hxu
  exact Section6.planarBrownianMotion_point_avoidance u x hxu.symm

end HarmonicBalls

import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity

/-! # The unit good-annulus event is measurable for a positive threshold (L2)

The hypothesis `hunit` of the earlier local reduction, `MeasurableSet {ν | IsGoodAnnulus ν 1 0 a b}`, is
discharged by the existing theorem `measurableSet_isGoodAnnulus_of_pos` (Proofs/Sec8/GoodEventPointPolarity.lean),
which needs only `0 < a`.
-/

open MeasureTheory Metric Set

namespace HarmonicBalls

/-- The unit good-annulus event is measurable for every positive threshold `a`. -/
theorem measurableSet_unitGoodAnnulus (a b : ℝ) (ha : 0 < a) :
    MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b} :=
  measurableSet_isGoodAnnulus_of_pos 1 one_pos 0 a b ha


end HarmonicBalls

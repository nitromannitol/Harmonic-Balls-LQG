import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Regular-open uniqueness from volume growth -/

namespace HarmonicBalls

universe u

/-- Lemma 9.4 follows from the full support supplied by volume growth. -/
theorem regularOpenEqOfAEEq_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : RegularOpenEqOfAEEqStmt.{u} :=
  regularOpenEqOfAEEq (lqgMeasureFullSupportStmt_of_volumeGrowth hI2)

end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Uniqueness of harmonic balls from volume growth

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

universe u

/-- Uniqueness follows from volume growth and the boundary and regular-open
comparison statements of Lemmas 9.3 and 9.4. -/
theorem uniquenessHarmonicBalls_of_boundary_and_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h93 : HarmonicBallBoundarySubsetStmt.{u}) (h94 : RegularOpenEqOfAEEqStmt.{u}) :
    UniquenessHarmonicBallsStmt.{u} :=
  uniquenessHarmonicBalls_of_boundary_and_fullSupport h93 h94
    (lqgMeasureFullSupportStmt_of_volumeGrowth hI2)

end HarmonicBalls

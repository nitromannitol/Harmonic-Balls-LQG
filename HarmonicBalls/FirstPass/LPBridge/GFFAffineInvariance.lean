import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Bridge: the LP affine invariance of the whole-plane GFF to the HB statement `WholePlaneGFFAffineInvariance`


`LatticeProb.LQG.AffineDerived.WholePlaneGFFAffineInvarianceLP` (`HarmonicBalls/LPStage/GFFAffineInvariance.lean`) is the
LP form of `HarmonicBalls.WholePlaneGFFAffineInvariance` (`HarmonicBalls/Proposed/LQG.lean:56`). The hypothesis and the
conclusion are the structure `IsWholePlaneGFF` of the two copies, transported along `isWholePlaneGFF_iff`
(`LPBridge/M1.lean`). The pairings and circle averages of the transformed field are the same expressions in both
statements. The HB definitions are kept and no counted declaration is changed.
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory

/-- The LP affine invariance of the whole-plane GFF implies the HB statement `HarmonicBalls.WholePlaneGFFAffineInvariance`
for the given `P hC hcirc`. -/
theorem wholePlaneGFFAffineInvariance_of_lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LatticeProb.LQG.AffineDerived.WholePlaneGFFAffineInvarianceLP P hC hcirc) :
    HarmonicBalls.WholePlaneGFFAffineInvariance P hC hcirc := by
  intro hG a ha b
  exact (isWholePlaneGFF_iff P _ _).2
    (h ((isWholePlaneGFF_iff P hC hcirc).1 hG) a ha b)

/-- The affine invariance of the whole-plane GFF holds in the HB form `HarmonicBalls.WholePlaneGFFAffineInvariance`, by the
LP proof `LatticeProb.LQG.AffineDerived.wholePlaneGFFAffineInvariance_lp` transported along
`wholePlaneGFFAffineInvariance_of_lp`. -/
theorem wholePlaneGFFAffineInvariance_lpStage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    HarmonicBalls.WholePlaneGFFAffineInvariance P hC hcirc :=
  wholePlaneGFFAffineInvariance_of_lp P hC hcirc
    (LatticeProb.LQG.AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc)

end HarmonicBalls.LPBridge

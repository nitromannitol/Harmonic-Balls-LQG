import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.LPBridge.M5c
import LatticeProb.LQG.WeylCompositionOuter2

/-!
# Bridge: the LP derived Weyl composition gives the frozen HB statement

`HarmonicBalls.weylMetricCompositionContinuousOuterFrozen_of_lpStage` proves the frozen statement
`WeylMetricCompositionContinuousOuterFrozen` (`FirstPass/Frozen/S11j.lean:117` of PHASE2-INVENTORY.md section 2)
from the LP statement `LatticeProb.LQG.weylMetricCompositionContinuousOuter_lp` (`LPStage/WeylCompositionOuter2.lean`).
No hypothesis is added. The length-metric predicate is transferred by the bridge `isEuclideanLengthMetric_iff_lpStage`
of `FirstPass/LPBridge/M5c.lean`; the Weyl scaling of the HB and LP copies agrees by definitional unfolding (as in M5c).
-/

namespace HarmonicBalls

/-- Bridge: the HB frozen `WeylMetricCompositionContinuousOuterFrozen` from its LP form
`LatticeProb.LQG.weylMetricCompositionContinuousOuter_lp`. -/
theorem weylMetricCompositionContinuousOuterFrozen_of_lpStage : WeylMetricCompositionContinuousOuterFrozen := by
  intro ξ hξ D g f hD hg hf hfin
  exact LatticeProb.LQG.weylMetricCompositionContinuousOuter_lp ξ hξ D g f
    ((isEuclideanLengthMetric_iff_lpStage D).mp hD) hg hf hfin

end HarmonicBalls

import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.WeylOffOrigin

/-!
# Bridge: the LP Weyl relation off the origin to the frozen HB statement

The LP statement `LatticeProb.LQG.LocalLQGInsertionWeylOffOriginLP` (`HarmonicBalls/LPStage/WeylOffOrigin.lean`) is the
LP form of `HarmonicBalls.LocalLQGInsertionWeylOffOrigin` (`HarmonicBalls/FirstPass/Frozen/S8c.lean:85`). Its two
hypothesis predicates are transported along the equivalences of the existing bridges:

* `isWholePlaneGFF_iff` (`LPBridge/M1.lean`): `HarmonicBalls.IsWholePlaneGFF` ↔ `LatticeProb.Gauss.IsWholePlaneGFF`;
* `isLQGMeasureOfField_iff` (`LPBridge/M4.lean`): `HarmonicBalls.IsLQGMeasureOfField` ↔ `LatticeProb.LQG.IsLQGMeasureOfField`.

The remaining binders and the conclusion are the same expression in both statements. The HB definitions are kept and
no counted declaration is changed.
-/

namespace HarmonicBalls.LPBridge

universe u

/-- The LP statement of the Weyl relation off the origin implies the frozen HB statement
`HarmonicBalls.LocalLQGInsertionWeylOffOrigin`. -/
theorem localLQGInsertionWeylOffOrigin_of_lp
    (h : LatticeProb.LQG.WeylOffOriginDerived.LocalLQGInsertionWeylOffOriginLP.{u}) :
    HarmonicBalls.LocalLQGInsertionWeylOffOrigin.{u} := by
  intro Ω _ P _ γ α₀ hC hcirc μ lam hGFF hγ0 hγ2 hα hμ hlam
  exact h Ω P γ α₀ hC hcirc μ lam ((isWholePlaneGFF_iff P hC hcirc).1 hGFF) hγ0 hγ2 hα
    ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ) ((isLQGMeasureOfField_iff P γ 0 hcirc lam).1 hlam)

/-- The Weyl relation off the origin, hypothesis-free: `HarmonicBalls.LocalLQGInsertionWeylOffOrigin` holds, by the
LP proof `LatticeProb.LQG.WeylOffOriginDerived.localLQGInsertionWeylOffOrigin_lp` transported along
`localLQGInsertionWeylOffOrigin_of_lp`. -/
theorem localLQGInsertionWeylOffOrigin_lpStage : HarmonicBalls.LocalLQGInsertionWeylOffOrigin.{u} :=
  localLQGInsertionWeylOffOrigin_of_lp LatticeProb.LQG.WeylOffOriginDerived.localLQGInsertionWeylOffOrigin_lp

end HarmonicBalls.LPBridge

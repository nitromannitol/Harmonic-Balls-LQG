import HarmonicBalls.FirstPass.Frozen.S11k
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.LPStage.LQGMassInner

/-!
# LP-stage bridge for the inner measurability of the LQG mass (row 33, z3)

`HarmonicBalls.lqgMassInnerMeasurable_of_lpStage` is the HB frozen statement `LQGMassInnerMeasurableFrozen`
(`FirstPass/Frozen/S11k.lean:66`), obtained from the unconditional LP statement
`LatticeProb.LQG.lqgMassInnerMeasurable_of_gff` (`LPStage/LQGMassInner.lean`) through the bridge equivalences of
`FirstPass/LPBridge/M1.lean` and `M4.lean`. Binder-free.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- `LQGMassInnerMeasurableFrozen` (row 33) from the LP stage, binder-free. -/
theorem lqgMassInnerMeasurable_of_lpStage : LQGMassInnerMeasurableFrozen.{u} := by
  intro γ α₀ Ω _ P _ hC hcirc μ hW h0 h1 h2 hμ O U hO hU hbdd hcl
  exact LatticeProb.LQG.lqgMassInnerMeasurable_of_gff P γ α₀ hC hcirc μ ((isWholePlaneGFF_iff P hC hcirc).1 hW)
    h0 h1 h2 ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ) O U hO hU hbdd hcl

end HarmonicBalls

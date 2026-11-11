import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.FirstPass.LPBridge.M5b
import HarmonicBalls.LPStage.WeylShiftedMass

/-!
# LP-stage bridge for the Weyl-shifted LQG mass (row 27, z4)

`HarmonicBalls.weylShiftedMassMeasurable_of_lpStage` is the HB frozen statement `WeylShiftedMassMeasurableFrozen`
(`FirstPass/Frozen/S11c.lean:233`), obtained from the unconditional LP statement
`LatticeProb.LQG.weylShiftedMassMeasurable_lp` (`LPStage/WeylShiftedMass.lean`) through the bridge equivalences
`isWholePlaneGFF_iff` (M1), `isLQGMeasureOfField_iff` (M4) and `isLQGMetricOfField_iff` (M5b). The HB and LP definitions
of `weylShiftPair` and of `IsClosedDyadicSquare` agree by unfolding (same bodies). Binder-free.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- `WeylShiftedMassMeasurableFrozen` (row 27) from the LP stage, binder-free. -/
theorem weylShiftedMassMeasurable_of_lpStage : WeylShiftedMassMeasurableFrozen.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα₀ Ω _ P hC hcirc μ D hW hμ hD f hf hfc hf0 S hS
  exact LatticeProb.LQG.weylShiftedMassMeasurable_lp.{u} γ α₀ ξ hγ0 hγ2 hα₀ Ω P hC hcirc μ D
    ((isWholePlaneGFF_iff P hC hcirc).1 hW) ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ)
    ((isLQGMetricOfField_iff P γ ξ α₀ hC D).1 hD) f hf hfc hf0 S hS

end HarmonicBalls

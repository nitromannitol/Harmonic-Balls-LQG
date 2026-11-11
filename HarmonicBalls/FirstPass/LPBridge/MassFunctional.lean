import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.LPStage.MassFunctional

/-!
# Measurability of the LQG mass of a closed set: frozen Prop from the LP stage

Binder-free proof of the frozen Prop `HarmonicBalls.LQGMassFunctionalMeasurableFrozen` (`HarmonicBalls/FirstPass/Frozen/S11d.lean:155`)
from the LP-stage theorem `LatticeProb.LQG.MassFunctionalDerived.lqgMassFunctionalMeasurable_lp`
(`HarmonicBalls/LPStage/MassFunctional.lean`). The HB and LP copies of the hypotheses and of the conclusion are
equivalent by `isWholePlaneGFF_iff` (`FirstPass/LPBridge/M1.lean`) and `isLQGMeasureOfField_iff`
(`FirstPass/LPBridge/M4.lean`); the functional spaces and the pairings agree by `rfl`
(`distributionMeasurableSpace_eq`, `addFunPairing_eq`).
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory

universe u

/-- The frozen mass-functional Prop `HarmonicBalls.LQGMassFunctionalMeasurableFrozen`, from the LP stage. -/
theorem lqgMassFunctionalMeasurable_of_lp : HarmonicBalls.LQGMassFunctionalMeasurableFrozen.{u} := by
  intro γ α₀ Ω _ P _ hC hcirc μ hW hγ hγ2 hα hμ S hS
  exact LatticeProb.LQG.MassFunctionalDerived.lqgMassFunctionalMeasurable_lp.{u} γ α₀ Ω P hC hcirc μ
    ((isWholePlaneGFF_iff P hC hcirc).mp hW) hγ hγ2 hα ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).mp hμ) S hS

end HarmonicBalls.LPBridge

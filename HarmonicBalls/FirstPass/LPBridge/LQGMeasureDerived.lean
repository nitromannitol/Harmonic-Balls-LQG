import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.LPStage.LQGMeasureDerived

/-!
# LP-stage bridge for the profile-decoder measurability

`HarmonicBalls.lqgMeasureOfProfileMeasurable_of_lpStage` is the HB Prop `LQGMeasureOfProfileMeasurableFrozen`
(`FirstPass/Frozen/S8d.lean:33`), obtained from the LP theorem
`LatticeProb.LQG.ProfileDerived.lqgMeasureOfProfileMeasurable_lp` (`LPStage/LQGMeasureDerived.lean`) through the
bridge equivalences of `FirstPass/LPBridge/M1.lean` and `M4.lean`. No other input is used.
-/

noncomputable section

namespace HarmonicBalls

open LPBridge

universe u

theorem lqgMeasureOfProfileMeasurable_of_lpStage : LQGMeasureOfProfileMeasurableFrozen.{u} := by
  intro Ω _ P _ γ α hC hcirc μ F hh hμ hFm hF
  have hh' := (isWholePlaneGFF_iff P hC hcirc).1 hh
  have hμ' := (isLQGMeasureOfField_iff P γ α hcirc μ).1 hμ
  obtain ⟨Dec, hDm, hDμ, hDlim⟩ :=
    LatticeProb.LQG.ProfileDerived.lqgMeasureOfProfileMeasurable_lp Ω P γ α hC hcirc μ F hh' hμ' hFm hF
  refine ⟨Dec, hDm, hDμ, ?_⟩
  exact hDlim.mono fun y hy => (isLQGLimit_iff _ _ _).2 hy

end HarmonicBalls

end

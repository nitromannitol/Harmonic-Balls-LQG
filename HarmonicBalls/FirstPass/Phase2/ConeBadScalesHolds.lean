import HarmonicBalls.FirstPass.S11c
import HarmonicBalls.FirstPass.Phase2.DerivedInputs40
import HarmonicBalls.FirstPass.Phase2.BallMassBoundsHolds
import HarmonicBalls.FirstPass.Phase2.CampbellRestrictionHolds
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.FirstPass.Phase2.CameronMartinLipschitzShiftHolds
import HarmonicBalls.FirstPass.Phase2.CoordChangeHolds
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Lemma 11.7 without hypotheses

`S11c.firstPass_11_7` proves Lemma 11.7 (`ManyConeBadScalesStmt`: many cone-bad dyadic scales at `μ_h`-almost every
point) by the internal dilation-ergodic argument and the local Palm transfer, from eight statements:
the cone-bad event probability (Lemma 11.8, `ConeBadEventProbabilityStmt`), the local Campbell marked restriction,
the measurability of the LQG measure of a profile, the common local decoder, Cameron-Martin absolute continuity for
locally Lipschitz shifts, and the coordinate change rule, existence and non-atomicity of the γ-LQG measure at every
insertion `α₀`. Each of the eight is now a theorem without hypotheses, so Lemma 11.7 holds outright. The counted form
`firstPass_11_7_derivedInputs43` instead binds the two retired statements `OriginRootedConeFrequencyFrozen` and
`RootedConeFrequencyTransferFrozen`, which are not used here.
-/

namespace HarmonicBalls

universe u

/-- Lemma 11.7 (`ManyConeBadScalesStmt`) with no hypothesis: `S11c.firstPass_11_7` with each of its eight hypotheses
supplied by a theorem. -/
theorem manyConeBadScalesStmt_holds : ManyConeBadScalesStmt.{u} :=
  S11c.firstPass_11_7.{u}
    (hPos := HarmonicBalls.Closure.closure_11_8_derivedInputs40.{u}
      (hDG := HarmonicBalls.wholePlaneLQGBallMassBounds_holds.{u}))
    (hCamp := localCampbellMarkedRestriction_holds.{u})
    (hDecFrozen := lqgMeasureOfProfileMeasurable_derived.{u})
    (hDec := LocalDecoderCommon.localLQGDecoderCommonFrozen_derived)
    (hCM := cameronMartinLocallyLipschitzShiftAbsCont_holds.{u})
    (hCC := fun γ α₀ Ω _ P hC hcirc => lqgMeasureCoordChange_holds.{u} Ω P γ α₀ hC hcirc)
    (hE := lqgMeasureExistence_forall_exponents.{u})
    (hNA := fun γ α₀ Ω _ P hC hcirc => lqgMeasureNonatomic_holds.{u} Ω P γ α₀ hC hcirc)

end HarmonicBalls

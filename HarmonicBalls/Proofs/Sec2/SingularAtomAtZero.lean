import HarmonicBalls.Proofs.Sec6.SingularityOriginNonatomic

/-! # Volume growth without a non-atomicity input

The hypotheses below are staged in `HarmonicBalls.Proposed.LQG` and remain
subject to source review. In particular, existence is needed at every
subcritical insertion strength, not just at zero. The origin atom is removed
using a strictly stronger insertion; the whole-plane mass estimate then gives
non-atomicity away from the origin. Neither argument assumes I2 or Lemma 2.4.

The four hypotheses are `WholePlaneLQGBallMassBounds` (Ding–Gwynne,
Lemma 3.8), `WholePlaneGFFAffineInvariance`, `LQGMeasureCoordChange` at zero,
and `LQGMeasureExistence` at every insertion. Their exact universally
quantified forms are the variables below; all are pending source review.
In particular, the cited existence sources have not been checked against the
same-space dyadic-limit interface at an arbitrary subcritical insertion.
The atom argument uses `Section6.ae_origin_nonatomic_of_stronger_existence`;
non-atomicity off zero uses the whole-plane multiscale estimate and the
punctured-plane weight identity. Weyl scaling follows from the limit definition.
The I2 producer then uses `BallMassReduction` and the dyadic all-scales
reduction; I1 follows from I2. No target-field non-atomicity is assumed.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ α hC hcirc)

include hDG hAff hCC hE

/-- The staged existence and whole-plane inputs imply the non-atomicity
interface, without assuming non-atomicity for the singular field. -/
theorem singular_nonatomic_of_existence_and_wholePlane :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α hC hcirc := by
  intro Ω _ P γ α hC hcirc
  exact Section6.lqgMeasureNonatomic_of_existence
    (wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG hAff hCC wholePlaneGFFMixtureStep_holds))
    P γ α hC hcirc (fun β => hE Ω P γ β hC hcirc)

/-- I2 follows from the staged whole-plane and existence inputs. -/
theorem lqgVolumeGrowthAllScalesStmt_of_stronger_singularity :
    LQGVolumeGrowthAllScalesStmt.{u} := by
  apply lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC
    (fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)
  exact singular_nonatomic_of_existence_and_wholePlane hDG hAff hCC hE

/-- I1 follows from the same staged inputs and the proved I2 implication. -/
theorem lqgMeasureFullSupportStmt_of_stronger_singularity :
    LQGMeasureFullSupportStmt.{u} :=
  lqgMeasureFullSupportStmt_of_volumeGrowth
    (lqgVolumeGrowthAllScalesStmt_of_stronger_singularity hDG hAff hCC hE)

end HarmonicBalls

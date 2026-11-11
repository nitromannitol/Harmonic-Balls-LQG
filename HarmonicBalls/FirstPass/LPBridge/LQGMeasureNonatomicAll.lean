import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11n.MeasureDecoder
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGMeasureNonatomicAll

/-!
# Bridge: the LP non-atomicity statements to the HB statements

`LatticeProb.LQG.LQGMeasureNonatomicLP` (`HarmonicBalls/LPStage/LQGMeasureNonatomic.lean`) is the LP form of
`HarmonicBalls.LQGMeasureNonatomic` (`HarmonicBalls/Proposed/LQG.lean:86`), and `LQGMeasureNonatomicAllLP`
(`LPStage/LQGMeasureNonatomicAll.lean`) is the LP form of `HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll`
(`HarmonicBalls/FirstPass/S11n/MeasureDecoder.lean:39`). The hypothesis predicates and the conclusion are transported along the
existing equivalences of the bridges: `isWholePlaneGFF_iff` (`LPBridge/M1.lean`) and `isLQGMeasureOfField_iff`
(`LPBridge/M4.lean`), as in `LPBridge/LQGWeylScaling.lean`.

The LP literature inputs `WholePlaneLQGBallMassBoundsLP`, `LQGMeasureCoordChangeLP` (at `α₀ = 0`) and `LQGMeasureExistenceLP`
are hypotheses of the bridge; they are not proved here and remain pending the operator's source check of their Proposed
counterparts. The HB definitions are kept and no counted declaration is changed.
-/

universe u

namespace HarmonicBalls.LPBridge

open MeasureTheory

/-- The LP non-atomicity statement implies the HB statement `HarmonicBalls.LQGMeasureNonatomic` for the given `P γ α₀ hC hcirc`. -/
theorem lqgMeasureNonatomic_of_lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LatticeProb.LQG.LQGMeasureNonatomicLP P γ α₀ hC hcirc) :
    HarmonicBalls.LQGMeasureNonatomic P γ α₀ hC hcirc := by
  intro hgff hγ0 hγ2 hα μ hμ
  filter_upwards [h ((isWholePlaneGFF_iff P hC hcirc).1 hgff) hγ0 hγ2 hα μ
    ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ)] with ω hω
  exact hω

/-- Row 41 in HB form: `HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll` from the LP literature inputs
(`LatticeProb.LQG.lqgMeasureNonatomicAll_lp`), transported by `lqgMeasureNonatomic_of_lp`. The inputs are hypotheses. -/
theorem lqgMeasureNonatomicAll_of_lp
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.LQGMeasureExistenceLP P γ α hC hcirc) :
    HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u} := by
  intro γ α₀ Ω _ P hC hcirc
  exact lqgMeasureNonatomic_of_lp P γ α₀ hC hcirc
    (LatticeProb.LQG.lqgMeasureNonatomicAll_lp hDG hCC hE γ α₀ Ω P hC hcirc)

end HarmonicBalls.LPBridge

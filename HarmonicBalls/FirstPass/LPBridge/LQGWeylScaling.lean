import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.LPStage.LQGWeylScaling

/-!
# Bridge: the LP Weyl scaling statement to the HB statement `LQGMeasureWeylScaling` (LPBridge, z6)

`LatticeProb.LQG.LQGWeylScalingDerived.LQGMeasureWeylScalingLP` (`HarmonicBalls/LPStage/LQGWeylScaling.lean`) is the LP form
of `HarmonicBalls.LQGMeasureWeylScaling` (`HarmonicBalls/Proposed/LQG.lean:107`). Its hypothesis predicates and its
conclusion are transported along the equivalences of the existing bridges:

* `isWholePlaneGFF_iff` (`LPBridge/M1.lean`): `HarmonicBalls.IsWholePlaneGFF` ↔ `LatticeProb.Gauss.IsWholePlaneGFF`;
* `isLQGMeasureOfField_iff` (`LPBridge/M4.lean`): `HarmonicBalls.IsLQGMeasureOfField` ↔ `LatticeProb.LQG.IsLQGMeasureOfField`;
* `isLQGLimit_iff` (`LPBridge/M4.lean`): `HarmonicBalls.IsLQGLimit` ↔ `LatticeProb.LQG.IsLQGLimit`, under the
  almost-sure quantifier;
* `lqgQ` and the circle averages agree by `rfl` (`lqgQ_eq`, `fieldCircleAverage_eq`), and so does `addCircleAverage`
  (the same body `fun r z => hε r z + Real.circleAverage f z r`).

The HB definitions are kept and no counted declaration is changed.
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory

/-- The LP Weyl scaling statement implies the HB statement `HarmonicBalls.LQGMeasureWeylScaling` for the given
`P γ α₀ hC hcirc`. -/
theorem lqgMeasureWeylScaling_of_lp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LatticeProb.LQG.LQGWeylScalingDerived.LQGMeasureWeylScalingLP P γ α₀ hC hcirc) :
    HarmonicBalls.LQGMeasureWeylScaling P γ α₀ hC hcirc := by
  intro hgff hγ0 hγ2 hα μ hμ
  filter_upwards [h ((isWholePlaneGFF_iff P hC hcirc).1 hgff) hγ0 hγ2 hα μ
    ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ)] with ω hω
  intro f hf
  exact (isLQGLimit_iff _ _ _).2 (hω f hf)

/-- The Weyl scaling statement `HarmonicBalls.LQGMeasureWeylScaling` holds, by the LP proof
`LatticeProb.LQG.LQGWeylScalingDerived.lqgMeasureWeylScaling_lp` transported along `lqgMeasureWeylScaling_of_lp`. -/
theorem lqgMeasureWeylScaling_lpStage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    HarmonicBalls.LQGMeasureWeylScaling P γ α₀ hC hcirc :=
  lqgMeasureWeylScaling_of_lp P γ α₀ hC hcirc
    (LatticeProb.LQG.LQGWeylScalingDerived.lqgMeasureWeylScaling_lp P γ α₀ hC hcirc)

end HarmonicBalls.LPBridge

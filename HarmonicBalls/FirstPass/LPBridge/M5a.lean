import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Draft.Section11
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.LPStage.LengthMetric

/-!
# Bridge to the staged length-metric definitions (module M5, deterministic half)

Each definition of `LatticeProb.LQG` in `HarmonicBalls/LPStage/LengthMetric.lean` is the same object as the corresponding
`HarmonicBalls` definition. The copies have the same bodies, so the bridges are `rfl`:
`curveLength`, `pathLength`, `internalMetric`, `internalDiam`, `IsLengthParametrized`, `weylScaling`, `weylShiftPair`.

The structure `IsEuclideanLengthMetric` is an inductive type and each copy is a different type, so no `rfl` relates the
two copies; its bridge is the `iff` `isEuclideanLengthMetric_iff`, which maps the six fields of one structure to the
six fields of the other.
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory Set
open scoped ENNReal NNReal

theorem curveLength_eq (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) (a b : ℝ) :
    HarmonicBalls.curveLength D p a b = LatticeProb.LQG.curveLength D p a b := rfl

theorem pathLength_eq (D : ℂ → ℂ → ℝ) {z w : ℂ} (P : Path z w) :
    HarmonicBalls.pathLength D P = LatticeProb.LQG.pathLength D P := rfl

theorem internalMetric_eq (D : ℂ → ℂ → ℝ) (U : Set ℂ) (z w : ℂ) :
    HarmonicBalls.internalMetric D U z w = LatticeProb.LQG.internalMetric D U z w := rfl

theorem internalDiam_eq (D : ℂ → ℂ → ℝ) (δ : ℝ) (A : Set ℂ) :
    HarmonicBalls.internalDiam D δ A = LatticeProb.LQG.internalDiam D δ A := rfl

theorem isLengthParametrized_eq (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) (T : ℝ) :
    HarmonicBalls.IsLengthParametrized D p T = LatticeProb.LQG.IsLengthParametrized D p T := rfl

theorem weylScaling_eq (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) (u v : ℂ) :
    HarmonicBalls.weylScaling D ξ f u v = LatticeProb.LQG.weylScaling D ξ f u v := rfl

theorem weylShiftPair_eq (γ ξ : ℝ) (f : ℂ → ℝ) (p : Measure ℂ × (ℂ → ℂ → ℝ)) :
    HarmonicBalls.weylShiftPair γ ξ f p = LatticeProb.LQG.weylShiftPair γ ξ f p := rfl

theorem isEuclideanLengthMetric_iff (D : ℂ → ℂ → ℝ) :
    HarmonicBalls.IsEuclideanLengthMetric D ↔ LatticeProb.LQG.IsEuclideanLengthMetric D where
  mp h := ⟨h.self_eq_zero, h.eq_of_eq_zero, h.symm, h.triangle, h.isOpen_iff, h.ofReal_eq_internalMetric⟩
  mpr h := ⟨h.self_eq_zero, h.eq_of_eq_zero, h.symm, h.triangle, h.isOpen_iff, h.ofReal_eq_internalMetric⟩

end HarmonicBalls.LPBridge

import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.Frozen.S11g
import LatticeProb.LQG.LengthMetricDerived

/-!
# Bridge: the staged LP derived length-metric statements give the frozen HB statements (module M5c)

`HarmonicBalls.weylScaledEuclideanFrozen_of_lpStage` and `HarmonicBalls.internalMetricClosedEqIInfThickeningFrozen_of_lpStage`
prove the frozen statements `WeylScaledEuclideanFrozen` and `InternalMetricClosedEqIInfThickeningFrozen`
(`FirstPass/Frozen/S11g.lean`) from the LP statements `LatticeProb.LQG.weylScaledEuclidean_derived` and
`LatticeProb.LQG.internalMetricClosedEqIInfThickening_derived` (`LatticeProb/LQG/LengthMetricDerived.lean`). No hypothesis is added.

The transfer uses the definitional equalities of the HB and LP copies of the length-metric definitions (`rfl`, as in
`FirstPass/LPBridge/M5a.lean`) and the bridge `isEuclideanLengthMetric_iff_lpStage` below. That bridge is a copy of
`HarmonicBalls.LPBridge.isEuclideanLengthMetric_iff` (`FirstPass/LPBridge/M5a.lean`). M5a is not imported here, because M5a
imports `LatticeProb/LQG/WeylInternalClosed.lean`, and the declarations of that file clash with those of
`LatticeProb/LQG/LengthMetricDerived.lean` (which copies them; "environment already contains ..." on import).
-/

namespace HarmonicBalls

/-- Bridge: the six fields of `HarmonicBalls.IsEuclideanLengthMetric D` and of `LatticeProb.LQG.IsEuclideanLengthMetric D`
correspond one to one (the two structures are different inductive types, so no `rfl` relates them). -/
theorem isEuclideanLengthMetric_iff_lpStage (D : ℂ → ℂ → ℝ) :
    IsEuclideanLengthMetric D ↔ LatticeProb.LQG.IsEuclideanLengthMetric D where
  mp h := ⟨h.self_eq_zero, h.eq_of_eq_zero, h.symm, h.triangle, h.isOpen_iff, h.ofReal_eq_internalMetric⟩
  mpr h := ⟨h.self_eq_zero, h.eq_of_eq_zero, h.symm, h.triangle, h.isOpen_iff, h.ofReal_eq_internalMetric⟩

/-- Bridge: the HB frozen `WeylScaledEuclideanFrozen` from its LP form `LatticeProb.LQG.weylScaledEuclidean_derived`. -/
theorem weylScaledEuclideanFrozen_of_lpStage : WeylScaledEuclideanFrozen := by
  intro D ξ f hD hf hc
  exact (isEuclideanLengthMetric_iff_lpStage _).mpr
    (LatticeProb.LQG.weylScaledEuclidean_derived D ξ f ((isEuclideanLengthMetric_iff_lpStage D).mp hD) hf hc)

/-- Bridge: the HB frozen `InternalMetricClosedEqIInfThickeningFrozen` from its LP form
`LatticeProb.LQG.internalMetricClosedEqIInfThickening_derived`. -/
theorem internalMetricClosedEqIInfThickeningFrozen_of_lpStage :
    InternalMetricClosedEqIInfThickeningFrozen := by
  intro D C hC hD x y hx hy
  exact LatticeProb.LQG.internalMetricClosedEqIInfThickening_derived D C hC
    ((isEuclideanLengthMetric_iff_lpStage D).mp hD) hx hy

end HarmonicBalls

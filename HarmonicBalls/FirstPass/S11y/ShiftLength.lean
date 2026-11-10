import HarmonicBalls.FirstPass.S11y.ShiftE3
import HarmonicBalls.FirstPass.S11m.WeylLengthCompact

/-!
# The shifted length metric, without a frozen input (Lemma 11.12, E3; z3 note §6.4)

`pinchLocal_E3_of_shift` takes the length-metric property of the shifted metric as a hypothesis `hE`.
This file discharges it deterministically. For a Euclidean length metric `D`, real `ξ`, and the shift weight
`ξ⁻¹ · log k · φ` with `φ` smooth and compactly supported, the real part of `weylScaling D ξ (shiftWeight3 ξ k φ)`
is again a Euclidean length metric (`weylScaling_continuous_compactSupport_length`,
FirstPass/S11m/WeylLengthCompact.lean). The frozen Prop `LQGMetricAlphaWeylShiftLengthFrozen` is not used.
-/

open MeasureTheory Set Metric Filter

namespace HarmonicBalls
namespace S11y

variable {D : ℂ → ℂ → ℝ}

/-- The shift weight `ξ⁻¹ · log k · φ` is continuous when `φ` is. -/
lemma shiftWeight3_continuous {ξ k : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) :
    Continuous (shiftWeight3 ξ k φ) := by
  unfold shiftWeight3
  exact continuous_const.mul (continuous_const.mul hφ)

/-- The shift weight `ξ⁻¹ · log k · φ` has compact support when `φ` does. -/
lemma shiftWeight3_hasCompactSupport {ξ k : ℝ} {φ : ℂ → ℝ} (hφc : HasCompactSupport φ) :
    HasCompactSupport (shiftWeight3 ξ k φ) := by
  unfold shiftWeight3
  exact hφc.comp_left (g := fun t : ℝ => ξ⁻¹ * (Real.log k * t)) (by simp)

/-- For a smooth compactly supported bump `φ`, the shifted metric
`(x, y) ↦ (weylScaling D ξ (ξ⁻¹ log k · φ) x y).toReal` is a Euclidean length metric (deterministic). -/
theorem shiftLength_of_bump (hD : IsEuclideanLengthMetric D) {ξ k : ℝ} {φ : ℂ → ℝ}
    (hφC : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    IsEuclideanLengthMetric (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal) :=
  (weylScaling_continuous_compactSupport_length D ξ _ hD
    (shiftWeight3_continuous hφC.continuous) (shiftWeight3_hasCompactSupport hφc)).2

/-- Lemma 11.12 (E3) for a bump shift, with the length property of the shifted metric derived
(`shiftLength_of_bump`) instead of assumed. Same conclusion as `pinchLocal_E3_of_shift`. -/
theorem pinchLocal_E3_of_shift_bump {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hD : IsEuclideanLengthMetric D) {μ : Measure ℂ} {γ ξ M c d k : ℝ}
    (hξ : 0 < ξ) (hk0 : 0 < k) (hk1 : k ≤ 1) (hc : 0 < c) (hkcd : k * d ≤ c / 2)
    {φ : ℂ → ℝ} (hφC : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ01 : ∀ z, φ z ∈ Icc (0 : ℝ) 1)
    (hφ1 : ∀ z ∈ closure (thickening δ (pinchK2 W V δ)), φ z = 1)
    (hφU : ∀ z ∈ closure U, φ z = 0) (hφout : ∀ z, z ∉ thickening (6 * δ) W → φ z = 0)
    (hE1 : pinchFirstEventLocal D W T Q' Q δ) (hE2 : pinchSecondEventLocal μ D U V δ M)
    (ha2 : c ≤ setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))
    (hd2 : internalDiam D δ (closure (thickening (3 * δ) W \ V)) ≤ ENNReal.ofReal d) :
    pinchFirstEventLocal (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal) W T Q' Q δ ∧
    pinchSecondEventLocal (μ.withDensity fun x => ENNReal.ofReal (Real.exp (γ * shiftWeight3 ξ k φ x)))
      (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal) U V δ M ∧
    pinchThirdEventLocal (fun x y => (weylScaling D ξ (shiftWeight3 ξ k φ) x y).toReal) V W δ :=
  pinchLocal_E3_of_shift hgeo hD hξ hk0 hk1 hc hkcd hφ01 hφ1 hφU hφout
    (shiftLength_of_bump hD hφC hφc) hE1 hE2 ha2 hd2

end S11y
end HarmonicBalls

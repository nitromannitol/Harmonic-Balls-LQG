import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.GFF

/-! # helper: constant shifts of the LQG approximations and limits

A constant additive shift `h ↦ h + c` of the circle-average profile multiplies the approximations
`ε^{γ²/2} e^{γ h_ε(z)} dz` (`lqgApprox`, Defs/LQG.lean:46) by the constant `e^{γ c}`, so the vague limit `IsLQGLimit`
(Defs/LQG.lean:49) is multiplied by the same constant. This is the deterministic form of the Weyl scaling by a constant
(Proposed/LQG.lean:93) at the level of the limit. It is used to normalize the affine-transformed field, whose circle
averages carry the constant `-hcirc ω 1 q` (`WholePlaneGFFAffineInvariance`, Proposed/LQG.lean:51).

Also `fieldCircleAverage 0 h = h` (the zero-order logarithmic term vanishes, Defs/GFF.lean:118).
No new mathematics: the statements are the definition of `lqgApprox`, `withDensity`, and the vague convergence. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- The approximation of a constant shift of the profile is the approximation multiplied by `e^{γ c}`. -/
theorem lqgApprox_add_const (γ : ℝ) (hε : ℝ → ℂ → ℝ) (c ε : ℝ) :
    lqgApprox γ (fun e z => hε e z + c) ε =
      ENNReal.ofReal (Real.exp (γ * c)) • lqgApprox γ hε ε := by
  unfold lqgApprox
  ext s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  show ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hε ε z + c)) = Real.exp (γ * c) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))
  rw [mul_add, Real.exp_add]
  ring

/-- The fixed-scale `fieldCircleAverage` of order zero is the circle-average profile itself. -/
theorem s8d_fieldCircleAverage_zero_eq (h : ℝ → ℂ → ℝ) : fieldCircleAverage 0 h = h := by
  funext r z
  simp [fieldCircleAverage]

/-- A constant shift of the profile transports the vague limit: if `m` is the `IsLQGLimit` of `hε`, then
`e^{γ c} • m` is the `IsLQGLimit` of `hε + c`. -/
theorem isLQGLimit_add_const (γ : ℝ) (hε : ℝ → ℂ → ℝ) (m : Measure ℂ) (c : ℝ)
    (h : IsLQGLimit γ hε m) :
    IsLQGLimit γ (fun e z => hε e z + c) (ENNReal.ofReal (Real.exp (γ * c)) • m) := by
  constructor
  · have hfin : IsLocallyFiniteMeasure ((Real.exp (γ * c)).toNNReal • m) := by
      have := h.isLocallyFiniteMeasure
      infer_instance
    simpa [ENNReal.ofReal, Measure.coe_nnreal_smul] using hfin
  · intro f hf hc
    have hlim := h.tendsto_integral f hf hc
    simp only [lqgApprox_add_const, integral_smul_measure, smul_eq_mul]
    exact hlim.const_mul _


end HarmonicBalls

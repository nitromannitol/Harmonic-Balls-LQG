import HarmonicBalls.Proofs.GFF.ContinuousCircleDilationMixing
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.Defs.LQG

/-! # FIRST-PASS helper (fp-S8d, owner n4): the dilated continuous circle profile, at positive scales

For a continuous circle-average profile `f` (`C(CircleParameter, ℝ)`, Bonanno-type version) the dilation
`continuousCircleDilation` (Proofs/GFF/ContinuousCircleDilationMixing.lean:19) is the affine pullback by `z ↦ z/2`
normalized at the unit point `(1/2, 0)`. At positive scales its circle profile is explicit:

* `s8d_circleProfile_dilation`: one step, `circleProfile (R f) r z = circleProfile f (r/2) (z/2) - circleProfile f (1/2) 0`;
* `s8d_circleProfile_dilation_iterate`: the `n`-fold iterate is the pullback by `(1/2)^n` normalized at `((1/2)^n, 0)`.

This is the deterministic input of the dilation identity of the LQG measure (the coordinate change with a constant shift,
`isLQGLimit_add_const` in ShiftLimit.lean). `s8d_isLQGLimit_congr_pos`: `IsLQGLimit` depends on the profile only at
positive scales, since the approximations `lqgApprox` are evaluated at dyadic scales. No new mathematics. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- One dilation step of the circle profile at positive radii. -/
theorem s8d_circleProfile_dilation (f : C(CircleParameter, ℝ)) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    circleProfile (continuousCircleDilation f) r z =
      circleProfile f (r / 2) (z / 2) - circleProfile f (1 / 2) 0 := by
  have h2 : (0 : ℝ) < r / 2 := by positivity
  have h12 : (0 : ℝ) < 1 / 2 := by norm_num
  unfold circleProfile continuousCircleDilation continuousCircleAffine
  simp only [hr, h2, h12, ↓reduceDIte]
  simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply,
    affineCircleParameter, ContinuousMap.coe_mk]
  congr 1
  · congr 1
    · apply Prod.ext
      · apply Subtype.ext
        simp
        ring
      · simp
        ring
  · congr 1
    · apply Prod.ext
      · apply Subtype.ext
        simp
      · simp

/-- The `(n+1)`-fold iterate of the dilation, at positive radii: the pullback by `(1/2)^{n+1}` normalized at the unit
point of that scale. -/
theorem s8d_circleProfile_dilation_iterate (f : C(CircleParameter, ℝ)) (n : ℕ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    circleProfile (continuousCircleDilation^[n + 1] f) r z =
      circleProfile f ((1 / 2 : ℝ) ^ (n + 1) * r) (((1 / 2 : ℝ) ^ (n + 1) : ℝ) * z) -
        circleProfile f ((1 / 2 : ℝ) ^ (n + 1)) 0 := by
  induction n generalizing r z with
  | zero =>
    simp only [zero_add, pow_one, Function.iterate_one]
    rw [s8d_circleProfile_dilation f hr z]
    congr 1
    · congr 1
      · ring
      · push_cast; ring
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hK : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    have h2 : (0 : ℝ) < r / 2 := by positivity
    rw [s8d_circleProfile_dilation _ hr z, ih h2 (z / 2), ih (by norm_num : (0 : ℝ) < 1 / 2) 0]
    have e1 : (1 / 2 : ℝ) ^ (n + 1) * (r / 2) = (1 / 2 : ℝ) ^ (n + 1 + 1) * r := by
      rw [pow_succ _ (n + 1)]
      ring
    have e2 : (1 / 2 : ℝ) ^ (n + 1) * (1 / 2) = (1 / 2 : ℝ) ^ (n + 1 + 1) := by
      rw [pow_succ _ (n + 1)]
    rw [e1, e2]
    have e3 : (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * (z / 2) = (((1 / 2 : ℝ) ^ (n + 1 + 1) : ℝ) : ℂ) * z := by
      rw [pow_succ _ (n + 1)]
      push_cast
      ring
    rw [e3]
    have e5 : (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) * 0 = 0 := by simp
    simp only [e5]
    ring

/-- `IsLQGLimit` depends on the profile only at positive scales (the approximations are taken at dyadic scales). -/
theorem s8d_isLQGLimit_congr_pos (γ : ℝ) {h h' : ℝ → ℂ → ℝ}
    (hh : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, h ε z = h' ε z) (m : Measure ℂ) :
    IsLQGLimit γ h m ↔ IsLQGLimit γ h' m := by
  have hA : ∀ k : ℕ, lqgApprox γ h (dyadicScale k) = lqgApprox γ h' (dyadicScale k) := by
    intro k
    unfold lqgApprox
    simp only [hh _ (dyadicScale_pos k)]
  constructor
  · intro H
    exact ⟨H.isLocallyFiniteMeasure, fun f hf hc => by
      simpa only [hA] using H.tendsto_integral f hf hc⟩
  · intro H
    exact ⟨H.isLocallyFiniteMeasure, fun f hf hc => by
      simpa only [← hA] using H.tendsto_integral f hf hc⟩

#print axioms s8d_circleProfile_dilation_iterate
#print axioms s8d_isLQGLimit_congr_pos

end HarmonicBalls

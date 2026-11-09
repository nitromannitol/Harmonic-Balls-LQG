import HarmonicBalls.FirstPass.S11d.SmoothCutoff

/-!
# Proposition 11.9, the shift function `g = -(c/ξ) φ` (fp-S11d, owner n3)

FIRST-PASS NEW. The shift of the field, `h~ = h - (φ/ξ) c` with `c = log(2A/ε) ≥ 0`, as a function `g = -(c/ξ) φ`
(paper proof, lines 3125-3131). Properties used downstream: smooth and compactly supported (Cameron-Martin hypothesis of
`CameronMartinGFFMutualAbsCont`); zero unit-circle average when `φ = 0` on the unit circle (`W ∩ ∂B₁ = ∅`); the Weyl weight
`ξ g = -c φ` is `-c` on `O` where `φ = 1`, and `≤ 0` everywhere.
-/

namespace HarmonicBalls

open Set Metric

/-- The shift `g = -(c/ξ) φ` has zero unit-circle average when `φ` vanishes on the unit circle. -/
theorem shift_circleAverage_zero {φ : ℂ → ℝ} {c ξ : ℝ} (hzero : ∀ z ∈ sphere (0 : ℂ) 1, φ z = 0) :
    Real.circleAverage (fun z => -(c / ξ) * φ z) 0 1 = 0 := by
  have hEq : Set.EqOn (fun z => -(c / ξ) * φ z) (fun _ => (0 : ℝ)) (sphere (0 : ℂ) |(1 : ℝ)|) := by
    intro z hz
    rw [abs_one] at hz
    simp [hzero z hz]
  rw [Real.circleAverage_congr_sphere hEq]
  exact Real.circleAverage_const 0 0 1

/-- The shift is smooth and compactly supported when `φ` is. -/
theorem shift_smooth_compact {φ : ℂ → ℝ} {c ξ : ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => -(c / ξ) * φ z) ∧ HasCompactSupport (fun z => -(c / ξ) * φ z) :=
  ⟨contDiff_const.mul hφs, HasCompactSupport.mul_left hφc⟩

/-- The Weyl weight of the shift: `ξ · (-(c/ξ) φ z) = -c φ z`, equal to `-c` where `φ = 1`. -/
theorem shift_weight_eq {φ : ℂ → ℝ} {c ξ : ℝ} (hξ : ξ ≠ 0) (z : ℂ) :
    ξ * (-(c / ξ) * φ z) = -(c * φ z) := by
  field_simp

/-- Upper bounds of the Weyl weight: `≤ 0` everywhere for `c ≥ 0` and `0 ≤ φ`; `= -c` where `φ = 1`. -/
theorem shift_weight_le {φ : ℂ → ℝ} {c ξ : ℝ} (hξ : ξ ≠ 0) (hc : 0 ≤ c) (hφ0 : ∀ z, 0 ≤ φ z) (z : ℂ) :
    ξ * (-(c / ξ) * φ z) ≤ 0 := by
  rw [shift_weight_eq hξ z]
  have := mul_nonneg hc (hφ0 z)
  linarith

end HarmonicBalls

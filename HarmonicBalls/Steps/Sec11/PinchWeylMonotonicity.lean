import HarmonicBalls.Steps.Sec11.WeylScalingOrder
import HarmonicBalls.Draft.Section11

/-! # Internal metric monotonicity for negative Weyl bumps

A nonpositive bump decreases the internal distances and diameters. The strict
third-event estimate needs additional local path control.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- Pointwise order of nonnegative distance values gives curve-length order. -/
theorem curveLength_le_of_ofReal_le {D E : ℂ → ℂ → ℝ}
    (h : ∀ x y, ENNReal.ofReal (D x y) ≤ ENNReal.ofReal (E x y))
    (p : ℝ → ℂ) (a b : ℝ) : curveLength D p a b ≤ curveLength E p a b := by
  unfold curveLength
  apply iSup_mono
  intro q
  apply Finset.sum_le_sum
  intro i hi
  exact h _ _

/-- Pointwise order of nonnegative distance values gives internal-distance order. -/
theorem internalMetric_le_of_ofReal_le {D E : ℂ → ℂ → ℝ}
    (h : ∀ x y, ENNReal.ofReal (D x y) ≤ ENNReal.ofReal (E x y))
    (U : Set ℂ) (x y : ℂ) : internalMetric D U x y ≤ internalMetric E U x y := by
  unfold internalMetric
  apply iInf_mono
  intro p
  apply iInf_mono
  intro hp
  exact curveLength_le_of_ofReal_le h p.extend 0 1

/-- Pointwise order of nonnegative distance values gives internal-diameter order. -/
theorem internalDiam_le_of_ofReal_le {D E : ℂ → ℂ → ℝ}
    (h : ∀ x y, ENNReal.ofReal (D x y) ≤ ENNReal.ofReal (E x y))
    (δ : ℝ) (A : Set ℂ) : internalDiam D δ A ≤ internalDiam E δ A := by
  unfold internalDiam
  apply iSup_mono
  intro x
  apply iSup_mono
  intro hx
  apply iSup_mono
  intro y
  apply iSup_mono
  intro hy
  exact internalMetric_le_of_ofReal_le h _ _ _

/-- A nonpositive perturbation of the Weyl exponent cannot increase any
internal diameter. The two real functions are explicit representatives of
the two Weyl-scaled distances. -/
theorem internalDiam_weyl_negative_bump_le (D : ℂ → ℂ → ℝ) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (f b : ℂ → ℝ) (hb : ∀ z, b z ≤ 0)
    (D₀ D₁ : ℂ → ℂ → ℝ)
    (hD₀ : ∀ x y, ENNReal.ofReal (D₀ x y) = weylScaling D ξ f x y)
    (hD₁ : ∀ x y, ENNReal.ofReal (D₁ x y) =
      weylScaling D ξ (fun z => f z + b z) x y)
    (δ : ℝ) (A : Set ℂ) : internalDiam D₁ δ A ≤ internalDiam D₀ δ A := by
  apply internalDiam_le_of_ofReal_le
  intro x y
  rw [hD₁ x y, hD₀ x y]
  apply weylScaling_mono_exponent
  intro z
  have h := mul_le_mul_of_nonneg_left (add_le_add_right (hb z) (f z)) hξ
  simpa only [add_zero] using h

end HarmonicBalls

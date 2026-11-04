import HarmonicBalls.Steps.Sec11.WeylBumpTopology
import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.PinchWeylMonotonicity

/-! # Quantitative constrained-path margin under a Weyl bump

A global lower bound on the weight gives a quantitative alternative to the
inverse Weyl identity. The price is a stronger original strict margin.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- A bounded nonpositive Weyl bump contracts set distances by at most its
global exponential lower bound. -/
theorem ofReal_setDist_weyl_negative_bump_lower
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ}
    (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    {A B : Set ℂ} (hA : A.Nonempty) (hB : B.Nonempty) :
    ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (setDist D A B) ≤
      ENNReal.ofReal (setDist (fun x y => (weylScaling D ξ f x y).toReal) A B) := by
  rw [ofReal_setDist_eq_iInf (D := fun x y => (weylScaling D ξ f x y).toReal) hA hB]
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  have hset : ENNReal.ofReal (setDist D A B) ≤ ENNReal.ofReal (D x y) := by
    rw [ofReal_setDist_eq_iInf hA hB]
    exact iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le y (iInf_le _ hy)))
  calc
    _ ≤ ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (D x y) := by gcongr
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        (weylScaling_negative_bump_real_bounds hD hξ f hl hu hzero x y).2.1

/-- A strict constrained-path margin survives a nonpositive Weyl bump when
it is smaller than the lower-bound multiple of the original set distance. -/
theorem constrainedPaths_of_weyl_negative_bump_margin
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ}
    (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    {A B S X : Set ℂ} (hA : A.Nonempty) (hB : B.Nonempty) (z : ℂ)
    (hmargin : (⨆ x ∈ X, internalMetric D S z x) <
      ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (setDist D A B)) :
    (⨆ x ∈ X, internalMetric (fun x y => (weylScaling D ξ f x y).toReal) S z x) <
      ENNReal.ofReal (setDist (fun x y => (weylScaling D ξ f x y).toReal) A B) := by
  have horder : ∀ x y, ENNReal.ofReal ((weylScaling D ξ f x y).toReal) ≤
      ENNReal.ofReal (D x y) := by
    intro x y
    exact ENNReal.ofReal_le_ofReal
      (weylScaling_negative_bump_real_bounds hD hξ f hl hu hzero x y).2.2
  have hgap := ofReal_setDist_weyl_negative_bump_lower hD hξ f hl hu hzero hA hB
  apply lt_of_le_of_lt ?_ (hmargin.trans_le hgap)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  exact le_iSup_of_le x (le_iSup_of_le hx (internalMetric_le_of_ofReal_le horder _ _ _))

end HarmonicBalls

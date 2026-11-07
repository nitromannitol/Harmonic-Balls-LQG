import HarmonicBalls.Steps.Sec11.WeylBoundaryGap
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds

/-! # Lower bounds for first-exit distances under Weyl scaling -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

private theorem positive_finite_mul_iInf {ι : Sort*} (c : ℝ≥0∞)
    (hc : 0 < c) (hct : c ≠ ∞) (F : ι → ℝ≥0∞) :
    c * (⨅ i, F i) = ⨅ i, c * F i := by
  classical
  by_cases h : Nonempty ι
  · let : Nonempty ι := h
    exact ENNReal.mul_iInf (fun h _ => (hct h).elim)
  · let : IsEmpty ι := not_nonempty_iff.mp h
    simp only [iInf_of_empty, ENNReal.mul_top (ne_of_gt hc)]

/-- A lower bound for the Weyl exponent on a neighborhood of a domain
controls the distance from an interior set to the domain boundary. -/
theorem ofReal_setDist_boundary_le_mul_of_inverse_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ L : ℝ} {f : ℂ → ℝ} {A U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hAU : A ⊆ U) (hUV : closure U ⊆ V)
    (hA : A.Nonempty) (hfront : (frontier U).Nonempty)
    (hlower : ∀ x ∈ V, L ≤ ξ * f x)
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y) :
    ENNReal.ofReal (setDist D A (frontier U)) ≤
      ENNReal.ofReal (Real.exp (-L)) * ENNReal.ofReal (setDist E A (frontier U)) := by
  have hnonnegD : ∀ x y, 0 ≤ D x y := by
    intro x y
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  rw [ofReal_setDist_boundary_eq_internalMetric hD hU hAU hUV hA hfront,
    ofReal_setDist_boundary_eq_internalMetric hE hU hAU hUV hA hfront]
  simp_rw [positive_finite_mul_iInf _ (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    ENNReal.ofReal_ne_top]
  refine iInf_mono fun x => iInf_mono fun hx => iInf_mono fun y => iInf_mono fun hy => ?_
  apply hE.internalMetric_weylScaling_le hD hnonnegD hV (hE.weylScaling_zero ξ) hreverse
  intro z hz
  have h := hlower z hz
  simp only [mul_neg]
  linarith

/-- The lower Weyl-exponent bound multiplies the boundary distance by at
least its exponential. -/
theorem ofReal_mul_setDist_boundary_le_of_inverse_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ L : ℝ} {f : ℂ → ℝ} {A U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hAU : A ⊆ U) (hUV : closure U ⊆ V)
    (hA : A.Nonempty) (hfront : (frontier U).Nonempty)
    (hlower : ∀ x ∈ V, L ≤ ξ * f x)
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y) :
    ENNReal.ofReal (Real.exp L) * ENNReal.ofReal (setDist D A (frontier U)) ≤
      ENNReal.ofReal (setDist E A (frontier U)) := by
  have h := ofReal_setDist_boundary_le_mul_of_inverse_weylScaling hD hE hU hV
    hAU hUV hA hfront hlower hreverse
  calc
    _ ≤ ENNReal.ofReal (Real.exp L) *
        (ENNReal.ofReal (Real.exp (-L)) * ENNReal.ofReal (setDist E A (frontier U))) :=
      by gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos L).le, ← Real.exp_add]
      simp

#print axioms ofReal_setDist_boundary_le_mul_of_inverse_weylScaling
#print axioms ofReal_mul_setDist_boundary_le_of_inverse_weylScaling

end HarmonicBalls

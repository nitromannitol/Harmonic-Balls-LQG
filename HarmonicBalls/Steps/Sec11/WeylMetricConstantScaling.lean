import HarmonicBalls.Steps.Sec11.CurveLengthReparam
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-! # Constant rescaling of a metric in the Weyl path formula -/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- Rescaling a metric by a positive constant rescales the natural parameter
of a length-parametrized path by the same constant. -/
theorem IsLengthParametrized.const_mul_reparam
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T c : ℝ} (hp : IsLengthParametrized D p T) (hc : 0 < c) :
    IsLengthParametrized (fun x y => c * D x y) (fun t => p (t / c)) (c * T) := by
  refine ⟨mul_nonneg hc.le hp.1, ?_, ?_⟩
  · apply hp.2.1.comp
    · exact (continuous_id.div_const c).continuousOn
    · intro t ht
      exact ⟨div_nonneg ht.1 hc.le, (div_le_iff₀ hc).2 (by simpa only [mul_comm] using ht.2)⟩
  · intro s t hs hst ht
    have hs' : 0 ≤ s / c := div_nonneg hs hc.le
    have hst' : s / c ≤ t / c := div_le_div_of_nonneg_right hst hc.le
    have ht' : t / c ≤ T := (div_le_iff₀ hc).2 (by simpa only [mul_comm] using ht)
    rw [curveLength_const_mul _ _ hc.le]
    change ENNReal.ofReal c * curveLength D (p ∘ fun t => t / c) s t = _
    rw [hD.curveLength_comp_of_monotoneOn p (fun t => t / c) hst
        (continuous_id.div_const c).continuousOn (fun _ _ _ _ h => div_le_div_of_nonneg_right h hc.le),
      hp.2.2 (s / c) (t / c) hs' hst' ht',
      ← ENNReal.ofReal_mul hc.le]
    congr 1
    field_simp

/-- Positive time dilation changes a lower integral by the same factor,
without requiring measurability of the integrand. -/
theorem lintegral_Icc_div_const (F : ℝ → ℝ≥0∞) (T : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Icc 0 (c * T), F (t / c) =
      ENNReal.ofReal c * ∫⁻ t in Icc 0 T, F t := by
  have hi : (fun t : ℝ => c * t) '' Icc 0 T = Icc 0 (c * T) := by
    simpa only [mul_zero] using image_mul_left_Icc' hc 0 T
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Icc 0 T) (f := fun t : ℝ => c * t)
    (f' := fun _ => c) measurableSet_Icc
    (fun x hx => (hasDerivAt_const_mul c).hasDerivWithinAt)
    (fun _ _ _ _ h => mul_left_cancel₀ hc.ne' h) (fun t => F (t / c))
  rw [hi] at h
  rw [h, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos hc]
  congr 1
  apply lintegral_congr
  intro t
  rw [mul_div_cancel_left₀ t hc.ne']

private theorem mul_iInf_of_pos_ne_top {ι : Sort*} (c : ℝ≥0∞)
    (hc : 0 < c) (hct : c ≠ ∞) (F : ι → ℝ≥0∞) :
    c * (⨅ i, F i) = ⨅ i, c * F i := by
  classical
  by_cases h : Nonempty ι
  · let : Nonempty ι := h
    exact ENNReal.mul_iInf (fun h _ => (hct h).elim)
  · let : IsEmpty ι := not_nonempty_iff.mp h
    simp only [iInf_of_empty, ENNReal.mul_top (ne_of_gt hc)]

/-- One direction of constant metric scaling in the Weyl path formula. -/
theorem IsEuclideanLengthMetric.weylScaling_const_mul_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {c : ℝ} (hc : 0 < c) (ξ : ℝ) (f : ℂ → ℝ) (u v : ℂ) :
    weylScaling (fun x y => c * D x y) ξ f u v ≤
      ENNReal.ofReal c * weylScaling D ξ f u v := by
  let a : ℝ≥0∞ := ENNReal.ofReal c
  have ha : 0 < a := ENNReal.ofReal_pos.mpr hc
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  change weylScaling (fun x y => c * D x y) ξ f u v ≤ a * weylScaling D ξ f u v
  unfold weylScaling
  simp_rw [mul_iInf_of_pos_ne_top a ha hat]
  apply le_iInf; intro T
  apply le_iInf; intro p
  apply le_iInf; intro hp
  apply le_iInf; intro hu
  apply le_iInf; intro hv
  have hp' := hp.const_mul_reparam hD hc
  refine iInf_le_of_le (c * T) (iInf_le_of_le (fun t => p (t / c)) ?_)
  refine iInf_le_of_le hp' ?_
  have hu' : p (0 / c) = u := by simpa using hu
  have hv' : p ((c * T) / c) = v := by simpa [hc.ne'] using hv
  refine iInf_le_of_le hu' (iInf_le_of_le hv' ?_)
  change (∫⁻ t in Icc 0 (c * T), (fun s => ENNReal.ofReal (Real.exp (ξ * f (p s)))) (t / c)) ≤ _
  exact le_of_eq (lintegral_Icc_div_const (fun s => ENNReal.ofReal (Real.exp (ξ * f (p s)))) T hc)

/-- Weyl scaling commutes with positive constant rescaling of the underlying
length metric, for an arbitrary weight. -/
theorem IsEuclideanLengthMetric.weylScaling_const_mul
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {c : ℝ} (hc : 0 < c) (ξ : ℝ) (f : ℂ → ℝ) (u v : ℂ) :
    weylScaling (fun x y => c * D x y) ξ f u v =
      ENNReal.ofReal c * weylScaling D ξ f u v := by
  apply le_antisymm (hD.weylScaling_const_mul_le hc ξ f u v)
  have hinv := (hD.const_mul hc).weylScaling_const_mul_le (inv_pos.mpr hc) ξ f u v
  change weylScaling (fun x y => c⁻¹ * (c * D x y)) ξ f u v ≤
    ENNReal.ofReal c⁻¹ * weylScaling (fun x y => c * D x y) ξ f u v at hinv
  simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hinv
  calc
    ENNReal.ofReal c * weylScaling D ξ f u v ≤
        ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ *
          weylScaling (fun x y => c * D x y) ξ f u v) :=
      by gcongr
    _ = weylScaling (fun x y => c * D x y) ξ f u v := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne',
        ENNReal.ofReal_one, one_mul]

#print axioms IsLengthParametrized.const_mul_reparam
#print axioms lintegral_Icc_div_const
#print axioms IsEuclideanLengthMetric.weylScaling_const_mul_le
#print axioms IsEuclideanLengthMetric.weylScaling_const_mul

end HarmonicBalls

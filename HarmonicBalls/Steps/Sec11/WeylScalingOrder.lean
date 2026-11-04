import HarmonicBalls.Defs.LQGMetric

/-! # Order properties of Weyl scaling

These identities compare Weyl scalings directly from their length-parametrized
path formula. They do not assert that a Weyl scaling is a length metric.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- Weyl scaling is monotone in the exponent of its weight. -/
theorem weylScaling_mono_exponent (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f g : ℂ → ℝ)
    (hfg : ∀ z, ξ * f z ≤ ξ * g z) (u v : ℂ) :
    weylScaling D ξ f u v ≤ weylScaling D ξ g u v := by
  unfold weylScaling
  apply iInf_mono
  intro T
  apply iInf_mono
  intro p
  apply iInf_mono
  intro hp
  apply iInf_mono
  intro hu
  apply iInf_mono
  intro hv
  exact lintegral_mono fun t => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hfg (p t)))

private theorem mul_iInf_of_pos_ne_top {ι : Sort*} (c : ℝ≥0∞)
    (hc : 0 < c) (hct : c ≠ ∞) (F : ι → ℝ≥0∞) :
    c * (⨅ i, F i) = ⨅ i, c * F i := by
  classical
  by_cases h : Nonempty ι
  · let : Nonempty ι := h
    exact ENNReal.mul_iInf (fun h _ => (hct h).elim)
  · let : IsEmpty ι := not_nonempty_iff.mp h
    simp only [iInf_of_empty, ENNReal.mul_top (ne_of_gt hc)]

/-- Adding a constant to the Weyl weight scales all distances by its
exponential factor, without assuming the original weight is measurable. -/
theorem weylScaling_add_const (D : ℂ → ℂ → ℝ) (ξ c : ℝ) (f : ℂ → ℝ)
    (u v : ℂ) :
    weylScaling D ξ (fun z => f z + c) u v =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScaling D ξ f u v := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * c))
  have ha : 0 < a := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  change weylScaling D ξ (fun z => f z + c) u v = a * weylScaling D ξ f u v
  unfold weylScaling
  simp_rw [mul_iInf_of_pos_ne_top a ha hat]
  apply iInf_congr
  intro T
  apply iInf_congr
  intro p
  apply iInf_congr
  intro hp
  apply iInf_congr
  intro hu
  apply iInf_congr
  intro hv
  rw [← lintegral_const_mul' a _ hat]
  apply lintegral_congr
  intro t
  dsimp [a]
  rw [mul_add, add_comm, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- A bounded negative Weyl bump leaves the scaled distance between the
original distance and its constant contraction. -/
theorem weylScaling_negative_bump_bounds (D : ℂ → ℂ → ℝ) {ξ c : ℝ}
    (hξ : 0 ≤ ξ) (f b : ℂ → ℝ) (hl : ∀ z, c ≤ b z)
    (hu : ∀ z, b z ≤ 0) (u v : ℂ) :
    ENNReal.ofReal (Real.exp (ξ * c)) * weylScaling D ξ f u v ≤
      weylScaling D ξ (fun z => f z + b z) u v ∧
    weylScaling D ξ (fun z => f z + b z) u v ≤ weylScaling D ξ f u v := by
  constructor
  · rw [← weylScaling_add_const]
    apply weylScaling_mono_exponent
    intro z
    exact mul_le_mul_of_nonneg_left (add_le_add_right (hl z) (f z)) hξ
  · apply weylScaling_mono_exponent
    intro z
    have h := mul_le_mul_of_nonneg_left (add_le_add_right (hu z) (f z)) hξ
    simpa only [add_zero] using h

end HarmonicBalls

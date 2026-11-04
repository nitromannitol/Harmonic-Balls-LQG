import HarmonicBalls.Proofs.Sec6.PlanarGaussianAverage
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup

/-! # Fubini's theorem for planar Gaussian averaging -/

namespace HarmonicBalls.Section6

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped ContDiff NNReal Topology

/-- Integration against the planar Gaussian is iterated one-dimensional
Gaussian integration in the two coordinate directions. -/
theorem integral_planarGaussian_eq_iterated {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) (t : ℝ≥0) :
    ∫ w, g w ∂planarGaussian z t =
      ∫ b, ∫ a, g ((a : ℂ) + (b : ℂ) * Complex.I)
        ∂gaussianReal z.re t ∂gaussianReal z.im t := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hgc
  have hc : Continuous (fun p : ℝ × ℝ => g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
      ((gaussianReal z.re t).prod (gaussianReal z.im t)) := by
    apply Integrable.of_bound hc.aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun p => hB _)
  rw [planarGaussian, integral_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable
    hg.aestronglyMeasurable]
  have heq : (fun p : ℝ × ℝ => g (Complex.measurableEquivRealProd.symm p)) =
      (fun p : ℝ × ℝ => g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    funext p
    congr 1
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
  rw [heq, integral_prod_symm _ hi]

/-- Averaging preserves a uniform error bound even when the probability
measure varies with the parameter. -/
theorem tendstoUniformly_integral_sub_of_tendstoUniformly
    {T X Y : Type*} [MeasurableSpace Y] (l : Filter T)
    (μ : T → X → Measure Y) (hμ : ∀ t x, IsProbabilityMeasure (μ t x))
    (F : T → X × Y → ℝ) (G : X × Y → ℝ)
    (hF : ∀ t x, Integrable (fun y => F t (x, y)) (μ t x))
    (hG : ∀ t x, Integrable (fun y => G (x, y)) (μ t x))
    (h : TendstoUniformly F G l) :
    TendstoUniformly
      (fun t x => (∫ y, F t (x, y) ∂μ t x) - ∫ y, G (x, y) ∂μ t x)
      (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  filter_upwards [h (ε / 2) (by linarith)] with t ht
  intro x
  have := hμ t x
  rw [Real.dist_eq, zero_sub, abs_neg, ← integral_sub (hF t x) (hG t x)]
  have hb : ‖∫ y, (F t (x, y) - G (x, y)) ∂μ t x‖ ≤ ε / 2 := by
    have hbound : ∀ᵐ y ∂μ t x, ‖F t (x, y) - G (x, y)‖ ≤ ε / 2 := by
      filter_upwards with y
      have hh := ht (x, y)
      rw [Real.dist_eq, abs_sub_comm] at hh
      simpa only [Real.norm_eq_abs] using le_of_lt hh
    simpa using norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at hb
  linarith

end HarmonicBalls.Section6

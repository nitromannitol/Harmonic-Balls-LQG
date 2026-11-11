import HarmonicBalls.Proofs.Potential.FiniteSourceObservationIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Weighted Green potentials at typical observers

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- Uniformly bounded source densities give mixed integrability and convergence
of the literal transposed Green potentials at almost every observer and in L¹. -/
theorem weighted_transposedGreen_observation_stability
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (C : ℝ)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hbound : ∀ n y, ‖f n y‖ ≤ C) (hgbound : ∀ y, ‖g y‖ ≤ C)
    (hconv : ∀ᵐ y ∂ν, Tendsto (fun n => f n y) atTop (𝓝 (g y))) :
    (∀ n, Integrable (fun p : ℂ × ℂ => f n p.1 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V))) ∧
    Integrable (fun p : ℂ × ℂ => g p.1 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) ∧
    (∀ᵐ x ∂μ.restrict V, Tendsto
      (fun n => ∫ y, f n y * greenFunction V y x ∂ν) atTop
      (𝓝 (∫ y, g y * greenFunction V y x ∂ν))) ∧
    Tendsto (fun n => ∫ x in V, ‖(∫ y, f n y * greenFunction V y x ∂ν) -
      (∫ y, g y * greenFunction V y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  have hp := generalDomain_green_integrable_product_of_local_upper_growth hup hV hVb hν
  have hprod (a : ℂ → ℝ) (ha : Measurable a) (hb : ∀ y, ‖a y‖ ≤ C) :
      Integrable (fun p : ℂ × ℂ => a p.1 * greenFunction V p.1 p.2)
        (ν.prod (μ.restrict V)) := by
    apply (hp.norm.const_mul C).mono' (((ha.comp measurable_fst).mul
      (measurable_greenFunction_uncurry hV)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖a p.1 * greenFunction V p.1 p.2‖ ≤ C * ‖greenFunction V p.1 p.2‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb p.1) (norm_nonneg _)
  have hi (n : ℕ) := hprod (f n) (hf n) (hbound n)
  have hj := hprod g hg hgbound
  have hpoint : ∀ᵐ x ∂μ.restrict V, Tendsto
      (fun n => ∫ y, f n y * greenFunction V y x ∂ν) atTop
      (𝓝 (∫ y, g y * greenFunction V y x ∂ν)) := by
    filter_upwards [hp.prod_left_ae] with x hx
    exact tendsto_integral_of_dominated_convergence
      (μ := ν) (fun y => C * ‖greenFunction V y x‖)
      (fun n => ((hf n).mul ((measurable_greenFunction_uncurry hV).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
      (hx.norm.const_mul C)
      (fun n => Eventually.of_forall fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound n y) (norm_nonneg _))
      (hconv.mono fun y hy => hy.mul tendsto_const_nhds)
  refine ⟨hi, hj, hpoint, ?_⟩
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := μ.restrict V) (fun x => (2 * C) * ∫ y, ‖greenFunction V y x‖ ∂ν)
    (fun n => (((hi n).integral_prod_right).sub hj.integral_prod_right).norm.aestronglyMeasurable)
    (hp.norm.integral_prod_right.const_mul (2 * C))
    (fun n => by
      filter_upwards [hp.prod_left_ae, (hi n).prod_left_ae, hj.prod_left_ae] with x hx hix hjx
      have hfn : (∫ y, ‖f n y * greenFunction V y x‖ ∂ν) ≤
          ∫ y, C * ‖greenFunction V y x‖ ∂ν := by
        apply integral_mono_ae hix.norm (hx.norm.const_mul C)
        exact Eventually.of_forall fun y => by
          change ‖f n y * greenFunction V y x‖ ≤ C * ‖greenFunction V y x‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hbound n y) (norm_nonneg _)
      have hgn : (∫ y, ‖g y * greenFunction V y x‖ ∂ν) ≤
          ∫ y, C * ‖greenFunction V y x‖ ∂ν := by
        apply integral_mono_ae hjx.norm (hx.norm.const_mul C)
        exact Eventually.of_forall fun y => by
          change ‖g y * greenFunction V y x‖ ≤ C * ‖greenFunction V y x‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hgbound y) (norm_nonneg _)
      rw [integral_const_mul] at hfn hgn
      change ‖‖(∫ y, f n y * greenFunction V y x ∂ν) -
        (∫ y, g y * greenFunction V y x ∂ν)‖‖ ≤ _
      rw [norm_norm]
      have ha := norm_integral_le_integral_norm (μ := ν) (fun y => f n y * greenFunction V y x)
      have hb := norm_integral_le_integral_norm (μ := ν) (fun y => g y * greenFunction V y x)
      have hc := norm_sub_le (∫ y, f n y * greenFunction V y x ∂ν)
        (∫ y, g y * greenFunction V y x ∂ν)
      nlinarith)
    (hpoint.mono fun x hx => by simpa using (hx.sub tendsto_const_nhds).norm)
  simpa using hlim


end HarmonicBalls

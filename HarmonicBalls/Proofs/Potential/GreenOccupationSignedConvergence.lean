import HarmonicBalls.Proofs.Potential.GreenOccupationSigned
import HarmonicBalls.Proofs.Potential.BrownianExitTimeExcess

/-! # Convergence of signed Brownian occupation integrals

Finite-horizon expectations converge to the Green integral, with an explicit error bound.
-/

open MeasureTheory Set Filter MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal Topology

namespace HarmonicBalls.GreenOccupation

/-- The expected exit-time excess is finite for every real horizon. -/
theorem lintegral_exitTime_sub_lt_top {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) (T : ℝ) :
    (∫⁻ p, ContinuousPath.exitTime D p - ENNReal.ofReal T
      ∂planarBrownianMotion x) < ⊤ := by
  exact lt_of_le_of_lt (lintegral_mono fun _ => tsub_le_self)
    (lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x)

/-- A real error bound for the finite-horizon signed occupation expectation. -/
theorem signed_occupation_error_le {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hfC : ∀ y, |f y| ≤ C)
    {T : ℝ} (hT : 0 ≤ T) :
    |(∫ y, (2 * greenFunction D x y) * f y) -
      (∫ p, (∫ t in Set.Ioi (0 : ℝ),
        (Set.Iic T).indicator (fun t =>
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
            (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x)| ≤
      C * (∫⁻ p, ContinuousPath.exitTime D p - ENNReal.ofReal T
        ∂planarBrownianMotion x).toReal := by
  have hC : 0 ≤ C := (abs_nonneg (f x)).trans (hfC x)
  have hfin := lintegral_exitTime_sub_lt_top
    (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) hD.1 x T
  have h := (signed_occupation_eq_green_and_error_le hD x hf hfC hT).2.2.2.2.2
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal (abs_nonneg _)] using hr

/-- Finite-horizon signed occupation expectations converge to the Green integral. -/
theorem tendsto_signed_occupation {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hfC : ∀ y, |f y| ≤ C) :
    Tendsto (fun T : ℝ =>
      ∫ p, (∫ t in Set.Ioi (0 : ℝ),
        (Set.Iic T).indicator (fun t =>
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
            (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x)
      atTop (𝓝 (∫ y, (2 * greenFunction D x y) * f y)) := by
  have hexcess := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_lintegral_exitTime_sub (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) hD.1 x)
  have hbound : Tendsto (fun T : ℝ => C * (∫⁻ p,
      ContinuousPath.exitTime D p - ENNReal.ofReal T ∂planarBrownianMotion x).toReal)
      atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, mul_zero, Function.comp_def] using tendsto_const_nhds.mul hexcess
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hbound
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  simpa only [Real.dist_eq, abs_sub_comm] using signed_occupation_error_le hD x hf hfC hT

end HarmonicBalls.GreenOccupation

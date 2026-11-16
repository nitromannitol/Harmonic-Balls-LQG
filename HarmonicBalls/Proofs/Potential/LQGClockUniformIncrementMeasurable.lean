import Mathlib
import HarmonicBalls.Defs.LBM

/-! # Measurable bounds for clock increments

Continuous fixed-scale fields give measurable pathwise bounds for uniform clock increments.
-/

namespace HarmonicBalls

open MeasureTheory Set MarkovProcess
open scoped NNReal Interval

/-- The integral of the absolute density increment is a measurable, finite, nonnegative
majorant for the clock increment on a bounded time interval. -/
theorem exists_measurable_lqgClock_uniform_increment_bound
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} (N k : ℕ)
    (h₁ : Continuous (hε (dyadicScale (k + 1))))
    (h₀ : Continuous (hε (dyadicScale k))) :
    ∃ a : ContinuousPath ℂ → ℝ, Measurable a ∧ (∀ b, 0 ≤ a b) ∧
      ∀ b (t : ℝ≥0), t ≤ (N : ℝ≥0) →
        |lqgClockApprox γ hε (dyadicScale (k + 1)) b t -
          lqgClockApprox γ hε (dyadicScale k) b t| ≤ a b := by
  let f : ContinuousPath ℂ → ℝ → ℝ := fun b s =>
    dyadicScale (k + 1) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale (k + 1)) (b s.toNNReal)) -
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) (b s.toNNReal))
  have hev : Continuous fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hf : Continuous (Function.uncurry f) := by
    dsimp [f, Function.uncurry]
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (h₁.comp hev)))).sub
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (h₀.comp hev))))
  have hfc (b : ContinuousPath ℂ) : Continuous (f b) :=
    hf.comp (continuous_const.prodMk continuous_id)
  refine ⟨fun b => ∫ s in (0 : ℝ)..(N : ℝ), |f b s|, ?_, ?_, ?_⟩
  · rw [show (fun b => ∫ s in (0 : ℝ)..(N : ℝ), |f b s|) =
        (fun b => ∫ s in Ioc (0 : ℝ) (N : ℝ), |f b s|) by
        funext b; rw [intervalIntegral.integral_of_le (by positivity)] ]
    exact hf.abs.measurable.stronglyMeasurable.integral_prod_right.measurable
  · intro b
    exact intervalIntegral.integral_nonneg_of_forall (by positivity) (fun s => abs_nonneg _)
  · intro b t ht
    have hti : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast ht
    have h1 : IntervalIntegrable (fun s => dyadicScale (k + 1) ^ (γ ^ 2 / 2) *
        Real.exp (γ * hε (dyadicScale (k + 1)) (b s.toNNReal))) volume 0 t :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        (h₁.comp (b.continuous.comp continuous_real_toNNReal))))).intervalIntegrable _ _
    have h0 : IntervalIntegrable (fun s => dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * hε (dyadicScale k) (b s.toNNReal))) volume 0 t :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        (h₀.comp (b.continuous.comp continuous_real_toNNReal))))).intervalIntegrable _ _
    rw [lqgClockApprox, lqgClockApprox, ← intervalIntegral.integral_sub h1 h0]
    exact (intervalIntegral.abs_integral_le_integral_abs (NNReal.coe_nonneg t)).trans
      (intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg t) hti
        (Filter.Eventually.of_forall fun s => abs_nonneg (f b s))
        ((hfc b).abs.intervalIntegrable _ _))

end HarmonicBalls

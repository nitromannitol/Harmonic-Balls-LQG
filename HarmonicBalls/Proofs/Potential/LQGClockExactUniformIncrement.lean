import HarmonicBalls.Proofs.Potential.LQGClockUniformIncrementMeasurable

/-! # Measurable uniform clock increments

The exact supremum of the clock increment on a bounded interval is measurable.
-/

namespace HarmonicBalls

open MeasureTheory Set MarkovProcess
open scoped NNReal ENNReal Interval

/-- The exact uniform clock increment is a finite measurable function of the path. -/
theorem exists_measurable_lqgClock_exact_uniform_increment
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} (N k : ℕ)
    (h₁ : Continuous (hε (dyadicScale (k + 1))))
    (h₀ : Continuous (hε (dyadicScale k))) :
    ∃ a : ContinuousPath ℂ → ℝ, Measurable a ∧
      (∀ b, a b = (⨆ t : Iic (N : ℝ≥0), ENNReal.ofReal
        |lqgClockApprox γ hε (dyadicScale (k + 1)) b t -
          lqgClockApprox γ hε (dyadicScale k) b t|).toReal) ∧
      (∀ b, 0 ≤ a b) ∧
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
  have heq (b : ContinuousPath ℂ) (t : ℝ≥0) :
      lqgClockApprox γ hε (dyadicScale (k + 1)) b t -
        lqgClockApprox γ hε (dyadicScale k) b t = ∫ s in (0 : ℝ)..(t : ℝ), f b s := by
    have h1 : IntervalIntegrable (fun s => dyadicScale (k + 1) ^ (γ ^ 2 / 2) *
        Real.exp (γ * hε (dyadicScale (k + 1)) (b s.toNNReal))) volume 0 t :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        (h₁.comp (b.continuous.comp continuous_real_toNNReal))))).intervalIntegrable _ _
    have h0 : IntervalIntegrable (fun s => dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * hε (dyadicScale k) (b s.toNNReal))) volume 0 t :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        (h₀.comp (b.continuous.comp continuous_real_toNNReal))))).intervalIntegrable _ _
    exact (intervalIntegral.integral_sub h1 h0).symm
  let q : Iic (N : ℝ≥0) → ContinuousPath ℂ → ℝ := fun t b =>
    |lqgClockApprox γ hε (dyadicScale (k + 1)) b t -
      lqgClockApprox γ hε (dyadicScale k) b t|
  have hqm (t : Iic (N : ℝ≥0)) : Measurable (q t) := by
    have hi : Measurable (fun b => ∫ s in (0 : ℝ)..((t : ℝ≥0) : ℝ), f b s) := by
      rw [show (fun b => ∫ s in (0 : ℝ)..((t : ℝ≥0) : ℝ), f b s) =
          (fun b => ∫ s in Ioc (0 : ℝ) ((t : ℝ≥0) : ℝ), f b s) by
          funext b; rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] ]
      exact hf.measurable.stronglyMeasurable.integral_prod_right.measurable
    convert hi.abs using 1
    funext b
    exact congrArg abs (heq b t)
  have hqc (b : ContinuousPath ℂ) : Continuous (fun t => q t b) := by
    have hc : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, f b s) :=
      intervalIntegral.continuous_primitive (fun a c => (hfc b).intervalIntegrable a c) 0
    have ht : Continuous (fun t : Iic (N : ℝ≥0) => ((t : ℝ≥0) : ℝ)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have h := (hc.comp ht).abs
    convert h using 1
    funext t
    exact congrArg abs (heq b t)
  let S : ContinuousPath ℂ → ℝ≥0∞ := fun b => ⨆ t, ENNReal.ofReal (q t b)
  have hSm : Measurable S := by
    convert measurable_iSup_of_lowerSemicontinuous
      (fun t => ENNReal.measurable_ofReal.comp (hqm t))
      (fun b => (ENNReal.continuous_ofReal.comp (hqc b)).lowerSemicontinuous) using 1
    ext b
    simp only [S, iSup_apply, Function.comp_apply]
  obtain ⟨A, _, hA0, hA⟩ := exists_measurable_lqgClock_uniform_increment_bound N k h₁ h₀
  have hSbound (b : ContinuousPath ℂ) : S b ≤ ENNReal.ofReal (A b) := by
    apply iSup_le
    intro t
    exact ENNReal.ofReal_le_ofReal (hA b t t.property)
  have hSfinite (b : ContinuousPath ℂ) : S b ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hSbound b)
  refine ⟨fun b => (S b).toReal, ENNReal.measurable_toReal.comp hSm, ?_, ?_, ?_⟩
  · intro b; rfl
  · intro b; exact ENNReal.toReal_nonneg
  · intro b t ht
    have hle : ENNReal.ofReal (q ⟨t, ht⟩ b) ≤ S b := le_iSup (fun u : Iic (N : ℝ≥0) => ENNReal.ofReal (q u b)) ⟨t, ht⟩
    have := ENNReal.toReal_mono (hSfinite b) hle
    simpa [q, ENNReal.toReal_ofReal (abs_nonneg _)] using this

end HarmonicBalls

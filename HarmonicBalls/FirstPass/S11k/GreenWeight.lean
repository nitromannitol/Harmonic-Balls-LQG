import HarmonicBalls.Defs.Annuli
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-!
# Weighted annular Green potential

Lemma 11.16 needs the annular Green supremum `annulusGreenPotentialSup` of the LQG measure at insertion `α`, which is a
continuous Weyl change of the measure at insertion `0` (`μ_α|A = |z|^{-γα} μ_0|A`). This file proves the measure-theoretic half, with no LQG input: a density bounded
by `C` on the annulus `annulus x₀ a b` gives a Green potential at most `C` times the unweighted one. The density
`|z|^{-c}` of `annulus 0 3 6` is bounded by `exp(|c| log 6)`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Weighted annular Green potential: if the density `w` is measurable and bounded by `C` on `annulus x₀ a b`, then
`SG_{a,b}(x₀)` of `μ.withDensity w` is at most `C` times `SG_{a,b}(x₀)` of `μ`. Pure measure theory; the supremum
over `x` and the Green integral over the annulus are unchanged in form. -/
theorem annulusGreenPotentialSup_withDensity_le (μ : Measure ℂ) {w : ℂ → ℝ≥0∞} (hw : Measurable w)
    (x₀ : ℂ) (a b : ℝ) (C : ℝ≥0∞) (hwC : ∀ y ∈ annulus x₀ a b, w y ≤ C) :
    annulusGreenPotentialSup (μ.withDensity w) x₀ a b ≤ C * annulusGreenPotentialSup μ x₀ a b := by
  unfold annulusGreenPotentialSup
  have hA : MeasurableSet (annulus x₀ a b) := measurableSet_ball.diff measurableSet_closedBall
  refine iSup₂_le fun x hx => ?_
  have hFm : Measurable fun y : ℂ => if y = x then (∞ : ℝ≥0∞) else
      ENNReal.ofReal (greenFunction (ball x₀ b) x y) :=
    Measurable.ite (measurableSet_singleton x) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  calc ∫⁻ y in annulus x₀ a b, (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y))
        ∂(μ.withDensity w)
      = ∫⁻ y in annulus x₀ a b, (w * fun y => if y = x then (∞ : ℝ≥0∞) else
          ENNReal.ofReal (greenFunction (ball x₀ b) x y)) y ∂μ :=
        setLIntegral_withDensity_eq_setLIntegral_mul μ hw hFm hA
    _ ≤ ∫⁻ y in annulus x₀ a b, C * (if y = x then (∞ : ℝ≥0∞) else
          ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ :=
        setLIntegral_mono' hA fun y hy => by
          simp only [Pi.mul_apply]
          gcongr
          exact hwC y hy
    _ = C * ∫⁻ y in annulus x₀ a b, (if y = x then (∞ : ℝ≥0∞) else
          ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ :=
        lintegral_const_mul _ hFm
    _ ≤ C * ⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b, (if y = x then (∞ : ℝ≥0∞) else
          ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ :=
        by gcongr; exact le_iSup₂ (f := fun x _ => ∫⁻ y in annulus x₀ a b, (if y = x then (∞ : ℝ≥0∞) else
          ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ) x hx

/-- For `3 < ‖z‖ < 6` the factor `exp(-c log ‖z‖)` is at most `exp(|c| log 6)`. -/
theorem exp_neg_mul_log_norm_le_of_mem_annulus (c : ℝ) {z : ℂ} (hz : z ∈ annulus 0 3 6) :
    Real.exp (-c * Real.log ‖z‖) ≤ Real.exp (|c| * Real.log 6) := by
  obtain ⟨h6, h3⟩ := hz
  rw [mem_ball_zero_iff] at h6
  rw [mem_closedBall_zero_iff, not_le] at h3
  have hlog3 : 0 < Real.log ‖z‖ := Real.log_pos (by linarith)
  have hlog6 : Real.log ‖z‖ ≤ Real.log 6 :=
    Real.log_le_log (by linarith) h6.le
  apply Real.exp_le_exp.2
  have h1 : -c * Real.log ‖z‖ ≤ |c| * Real.log ‖z‖ :=
    mul_le_mul_of_nonneg_right (by linarith [neg_le_abs c]) hlog3.le
  have h2 : |c| * Real.log ‖z‖ ≤ |c| * Real.log 6 :=
    mul_le_mul_of_nonneg_left hlog6 (abs_nonneg c)
  linarith

/-- Corollary for the Weyl factor of the LQG measure: the density `exp(-c log|z|)` (with `c = γα`) on the annulus
`annulus 0 3 6` is bounded, so the annular Green supremum of the Weyl-changed measure is at most a deterministic constant
times that of `μ`. -/
theorem annulusGreenPotentialSup_weylLog_le (μ : Measure ℂ) (c : ℝ) :
    annulusGreenPotentialSup (μ.withDensity fun z => ENNReal.ofReal (Real.exp (-c * Real.log ‖z‖))) 0 3 6 ≤
      ENNReal.ofReal (Real.exp (|c| * Real.log 6)) * annulusGreenPotentialSup μ 0 3 6 := by
  refine annulusGreenPotentialSup_withDensity_le μ ?_ 0 3 6 _ fun y hy => ?_
  · exact (Real.measurable_exp.comp (measurable_const.mul
      (Real.measurable_log.comp continuous_norm.measurable))).ennreal_ofReal
  · exact ENNReal.ofReal_le_ofReal (exp_neg_mul_log_norm_le_of_mem_annulus c hy)

end HarmonicBalls

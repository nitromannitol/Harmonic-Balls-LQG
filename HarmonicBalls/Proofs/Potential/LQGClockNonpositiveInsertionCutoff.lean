import HarmonicBalls.Proofs.Potential.LQGClockInnerProduct

/-! # Fine-scale comparison for nonpositive insertions

Inner occupations for negative insertions are controlled by their zero-insertion counterparts.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- On a ball of radius `δ`, a nonpositive insertion contributes a factor at most
`δ ^ (-γ * α)` at every positive smoothing scale at most `δ`. -/
theorem inner_nonpositive_inserted_clock_le_zero
    (h : ℝ → ℂ → ℝ) (γ α δ ε a b : ℝ) (path : ContinuousPath ℂ)
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε) (hεδ : ε ≤ δ) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α h ε z)) (path s.toNNReal))) ≤
      ENNReal.ofReal (δ ^ (-γ * α)) *
        (∫⁻ s in Ioc a b, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 h ε z)) (path s.toNNReal))) := by
  have hδ : 0 < δ := lt_of_lt_of_le hε hεδ
  have hcoeff : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro s
  let z := path s.toNNReal
  change ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator _ z) ≤
    ENNReal.ofReal (δ ^ (-γ * α)) * ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator _ z)
  simp only [Set.indicator_apply]
  split_ifs with hz
  · have hm : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
    have hmδ : max ε ‖z‖ ≤ δ := max_le hεδ (le_of_lt hz)
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
        Real.log (max ε ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hε)
    have hpow : 0 ≤ ε ^ (γ ^ 2 / 2) := Real.rpow_nonneg hε.le _
    have hfactor : Real.exp ((-γ * α) * Real.log (max ε ‖z‖)) ≤ δ ^ (-γ * α) := by
      rw [Real.rpow_def_of_pos hδ]
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Real.log_le_log hm hmδ) hcoeff
    have heq : γ * LatticeProb.Gauss.fieldCircleAverage α h ε z =
        γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z +
          (-γ * α) * Real.log (max ε ‖z‖) := by
      dsimp [LatticeProb.Gauss.fieldCircleAverage]
      rw [hlog]
      ring
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    apply ENNReal.ofReal_le_ofReal
    rw [heq, Real.exp_add]
    have hmultip := mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg hpow (Real.exp_pos (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z)).le)
    nlinarith [hmultip]
  · simp

/-- The same comparison holds simultaneously for a countable family of fine scales. -/
theorem iSup_inner_nonpositive_inserted_clock_le_zero
    (h : ℝ → ℂ → ℝ) (γ α δ a b : ℝ) (path : ContinuousPath ℂ)
    (ε : ℕ → ℝ) (hγ : 0 ≤ γ) (hα : α ≤ 0)
    (hε : ∀ n, 0 < ε n) (hεδ : ∀ n, ε n ≤ δ) :
    (⨆ n, ∫⁻ s in Ioc a b, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ}.indicator (fun z => (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α h (ε n) z)) (path s.toNNReal))) ≤
      ENNReal.ofReal (δ ^ (-γ * α)) *
        (⨆ n, ∫⁻ s in Ioc a b, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z => (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 h (ε n) z)) (path s.toNNReal))) := by
  apply iSup_le
  intro n
  exact (inner_nonpositive_inserted_clock_le_zero h γ α δ (ε n) a b path hγ hα
    (hε n) (hεδ n)).trans (mul_le_mul_right (le_iSup (fun n =>
      ∫⁻ s in Ioc a b, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 h (ε n) z)) (path s.toNNReal))) n) _)

end HarmonicBalls

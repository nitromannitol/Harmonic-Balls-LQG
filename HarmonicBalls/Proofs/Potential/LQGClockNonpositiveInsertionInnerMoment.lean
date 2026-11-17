import HarmonicBalls.Proofs.Potential.LQGClockInnerProduct

/-! # Inner clock occupation for nonpositive insertion

A uniform small-radius first-moment bound for the inserted clock occupation.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Nonpositive insertions have a uniform power bound on their inner clock occupation. -/
theorem exists_lintegral_prod_brownian_inner_nonpositive_inserted_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α : ℝ) (hγ : 0 < γ) (hγtwo : γ < 2) (hα : α ≤ 0) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧ ∀ {ε δ : ℝ}, 0 < ε → ε ≤ 1/2 →
      0 < δ → δ ≤ 1/2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤ (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) * C := by
  have hγpos : 0 < γ := (show γ ∈ Ioo (0 : ℝ) 2 from ⟨hγ, hγtwo⟩).1
  have hq : γ * γ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hγpos)
  have hp : (3 / 2 : ℝ) - γ * γ⁻¹ = 1 / 2 := by rw [hq]; norm_num
  obtain ⟨C, hC, hbound⟩ := exists_lintegral_prod_brownian_inner_inserted_le
    hh x γ γ⁻¹ (3 / 2) (by rw [hq]; norm_num) (by rw [hq]; norm_num) (by norm_num)
  refine ⟨C + 1, by positivity, ENNReal.add_lt_top.mpr ⟨hC, by simp⟩, ?_⟩
  intro ε δ hε hεhalf hδ hδhalf
  have hcomp (ω : Ω) (z : ℂ) (hz : ‖z‖ < δ) :
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z ≤
      LatticeProb.Gauss.fieldCircleAverage γ⁻¹ (hcirc ω) ε z := by
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
        Real.log (max ε ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hε)
    have hlogle : Real.log (max ε ‖z‖) ≤ 0 :=
      Real.log_nonpos (le_of_lt (lt_max_of_lt_left hε)) (max_le (by linarith) (by linarith))
    have hαβ : α ≤ γ⁻¹ := hα.trans (le_of_lt (inv_pos.mpr hγ))
    have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hαβ) hlogle
    dsimp [LatticeProb.Gauss.fieldCircleAverage]
    rw [hlog]
    linarith
  calc
    _ ≤ (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage γ⁻¹ (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) := by
      apply lintegral_mono
      intro q
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      simp only [Set.indicator_apply]
      split_ifs with hz
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hcomp q.1 _ hz) (le_of_lt hγ)))
          (Real.rpow_nonneg (le_of_lt hε) _)
      · exact le_rfl
    _ ≤ (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) * C := by
      simpa only [hp] using hbound hε hεhalf hδ hδhalf
    _ ≤ _ := by gcongr; exact le_add_right le_rfl

end HarmonicBalls

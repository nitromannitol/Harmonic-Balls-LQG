import HarmonicBalls.Proofs.Potential.LQGClockInnerProduct
import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation

/-! # Diagonal inner clock occupation

Summability of actual inserted clock occupation at matched dyadic scales and radii.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- At matched dyadic smoothing scales and cutoff radii, the inner occupations
are summable almost surely under the product of the field and Brownian laws. -/
theorem ae_tsum_inner_inserted_dyadic_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (∑' n : ℕ, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          ((2 : ℝ)⁻¹ ^ (n + 1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ((2 : ℝ)⁻¹ ^ (n + 1)) z))
              (q.2 s.toNNReal))) < ∞ := by
  let δ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδhalf (n : ℕ) : δ n ≤ 1 / 2 := by
    dsimp [δ]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let F (n : ℕ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ n}.indicator (fun z => (δ n) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (δ n) z)) (q.2 s.toNNReal))
  have hF (n : ℕ) : AEMeasurable (F n) (P.prod (planarBrownianMotion x)) :=
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) (hδ n) γ α (δ n) 0 1
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_inner_inserted_le hh x γ α p hq hqp hp
  have he : 0 < p - γ * α := sub_pos.mpr hqp
  have hsum : (∑' n : ℕ, ENNReal.ofReal ((δ n) ^ (p - γ * α)) * C) < ∞ := by
    rw [ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top _ hC
    exact (ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h)
      (fun n : ℕ => ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ (p - γ * α)))).trans_lt
        (tsum_dyadic_rpow_lt_top he)
  have hint : (∫⁻ q, ∑' n, F n q ∂(P.prod (planarBrownianMotion x))) < ∞ := by
    rw [lintegral_tsum hF]
    refine (ENNReal.tsum_le_tsum fun n => ?_).trans_lt hsum
    have hn := hbound (hδ n) (hδhalf n) (hδ n) (hδhalf n)
    rw [ENNReal.ofReal_rpow_of_nonneg (hδ n).le he.le] at hn
    exact hn
  exact ae_lt_top' (AEMeasurable.tsum hF) hint.ne

end HarmonicBalls

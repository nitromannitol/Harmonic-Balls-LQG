import HarmonicBalls.Proofs.Potential.BrownianAllHorizonDyadicPairCount
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-! # Shifted dyadic pair counts up to Brownian exit

The shifted-grid close-pair bound holds up to exit from a bounded ball.
-/

open MeasureTheory MarkovProcess
open scoped ENNReal

namespace HarmonicBalls

/-- For a finite exit, the grid endpoint is the genuine extended exit time. -/
theorem mem_shiftedDyadicIndicesUntil_exitTime (D : Set ℂ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ∞) (s : ℝ) (k : ℕ) (i : ℤ) :
    i ∈ shiftedDyadicIndicesUntil (ContinuousPath.exitTime D b).toReal s k ↔
      0 ≤ s + (1 / 4 : ℝ) ^ k * (i : ℝ) ∧
        ENNReal.ofReal (s + (1 / 4 : ℝ) ^ k * (i : ℝ)) ≤
          ContinuousPath.exitTime D b := by
  rw [mem_shiftedDyadicIndicesUntil, Set.mem_Icc,
    ENNReal.ofReal_le_iff_le_toReal hfin]

/-- A Brownian path has finite exit time from a ball and the shifted-grid pair bound
up to that exit, including both endpoints of the grid interval. -/
theorem planarBrownianMotion_shifted_dyadic_close_pairs_until_ball_exit
    (x z : ℂ) (R : ℝ) :
    ∀ᵐ b ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (Metric.ball z R) b < ∞ ∧
      ENNReal.ofReal (ContinuousPath.exitTime (Metric.ball z R) b).toReal =
        ContinuousPath.exitTime (Metric.ball z R) b ∧
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ,
        (sampledClosePairCount (fun t => b (Real.toNNReal t))
          (shiftedDyadicIndicesUntil (ContinuousPath.exitTime (Metric.ball z R) b).toReal s k)
          (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ)) ((1 / 2 : ℝ) ^ k) : ℝ) ≤
            C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
  filter_upwards [planarBrownianMotion_shifted_dyadic_close_pairs_all_horizons x,
    Section6.ae_planarBrownian_exitTime_bounded_lt_top x (Metric.isBounded_ball :
      Bornology.IsBounded (Metric.ball z R))] with b hb hfin
  exact ⟨hfin, ENNReal.ofReal_toReal hfin.ne, hb _ ENNReal.toReal_nonneg⟩

end HarmonicBalls

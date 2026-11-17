import HarmonicBalls.Proofs.Potential.BrownianSharpStoppedDomainOccupation
import HarmonicBalls.Proofs.Potential.BrownianAllHorizonBallOccupation
import LatticeProb.Analysis.LogKernel

/-! # Logarithmic tails of stopped Brownian occupation

Uniform subcritical ball occupation bounds control the logarithmic potential near its pole.
-/

open MeasureTheory MarkovProcess Set Metric Filter
open scoped ENNReal

namespace HarmonicBalls

/-- A power bound on dyadic ball masses controls the local logarithmic potential. -/
theorem setLIntegral_ball_log_le_of_power {μ : Measure ℂ} {z : ℂ} {r d C : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hC : 0 ≤ C)
    (hvol : ∀ k : ℕ, μ (ball z (r * (1 / 2) ^ k)) ≤
      ENNReal.ofReal (C * (r * (1 / 2) ^ k) ^ d)) :
    ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ ≤
      ENNReal.ofReal ((Real.log (1 / r) + 1 + Real.log 2) * C * r ^ d *
        (1 - (1 / 2) ^ d)⁻¹) := by
  have hc : 0 ≤ Real.log (1 / r) + 1 + Real.log 2 := by
    have h1 := Real.log_nonneg (show (1 : ℝ) ≤ 1 / r by rw [le_div_iff₀ hr]; linarith)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  let c := Real.log (1 / r) + 1 + Real.log 2
  calc ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
      ≤ ∫⁻ w in ball z r, ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator
          (fun _ => ENNReal.ofReal c) w ∂μ := by
        exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2
          (Eventually.of_forall fun w hw => LatticeProb.LogKernel.ofReal_log_le_tsum_indicator hr hr1 hw))
    _ ≤ ∫⁻ w, ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator
          (fun _ => ENNReal.ofReal c) w ∂μ := setLIntegral_le_lintegral _ _
    _ = ∑' k : ℕ, ENNReal.ofReal c * μ (ball z (r * (1 / 2) ^ k)) := by
        rw [lintegral_tsum fun k => (measurable_const.indicator measurableSet_ball).aemeasurable]
        exact tsum_congr fun k => lintegral_indicator_const measurableSet_ball _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((c * C) * (r * (1 / 2) ^ k) ^ d) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [show (c * C) * (r * (1 / 2) ^ k) ^ d =
          c * (C * (r * (1 / 2) ^ k) ^ d) by ring, ENNReal.ofReal_mul hc]
        exact mul_le_mul_right (hvol k) _
    _ = ENNReal.ofReal ((c * C) * r ^ d * (1 - (1 / 2) ^ d)⁻¹) :=
      LatticeProb.LogKernel.tsum_ofReal_mul_rpow_half_pow (mul_nonneg hc hC) hr.le hd

/-- On one full-mass event, the stopped logarithmic potential has a uniform subcritical
power bound for every bounded domain and every center. -/
theorem planarBrownianMotion_stopped_uniform_log_potential_tail (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      ∀ d : ℝ, 0 < d → d < 2 → ∃ C : ℝ, 0 < C ∧
        ∀ (z : ℂ) (r : ℝ), 0 < r → r ≤ 1 →
          ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1)
            ∂(stoppedBrownianOccupation D b) ≤
          ENNReal.ofReal ((Real.log (1 / r) + 1 + Real.log 2) * C * r ^ d *
            (1 - (1 / 2) ^ d)⁻¹) := by
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  filter_upwards [planarBrownianMotion_uniform_ball_occupation_all_horizons x, hballs] with b hb hball D hD d hd hd2
  obtain ⟨R, hR⟩ := hD.subset_ball x
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : D ⊆ ball x (n : ℝ) := hR.trans (ball_subset_ball hn)
  have hfin : ContinuousPath.exitTime D b < ∞ :=
    lt_of_le_of_lt (ContinuousPath.exitTime_mono hsub b) (hball n)
  obtain ⟨C, hC, hbound⟩ := hb (ContinuousPath.exitTime D b).toReal d hd hd2
  refine ⟨C, hC, fun z r hr hr1 => setLIntegral_ball_log_le_of_power hr hr1 hd hC.le ?_⟩
  intro k
  have hp : 0 < r * (1 / 2 : ℝ) ^ k := by positivity
  have hs : r * (1 / 2 : ℝ) ^ k ≤ 1 :=
    (mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))).trans hr1
  exact (stoppedBrownianOccupation_ball_le D b hfin.ne z _).trans (hbound z _ hp hs)

end HarmonicBalls

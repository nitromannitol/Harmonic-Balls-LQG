import HarmonicBalls.Proofs.Potential.BrownianStoppedDyadicPairCount

/-! # Shifted dyadic pair counts up to bounded-domain exit

One almost-sure event gives the shifted-grid close-pair bound up to exit from
all bounded domains, with constants depending on the path and domain.
-/

open MeasureTheory MarkovProcess
open scoped ENNReal

namespace HarmonicBalls

/-- For each starting point, one almost-sure event gives finite exit and the
shifted-grid close-pair bound for every bounded set, including both endpoints. -/
theorem planarBrownianMotion_shifted_dyadic_close_pairs_until_all_bounded_exits
    (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      ContinuousPath.exitTime D b < ∞ ∧
      ENNReal.ofReal (ContinuousPath.exitTime D b).toReal = ContinuousPath.exitTime D b ∧
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ,
        (sampledClosePairCount (fun t => b (Real.toNNReal t))
          (shiftedDyadicIndicesUntil (ContinuousPath.exitTime D b).toReal s k)
          (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ)) ((1 / 2 : ℝ) ^ k) : ℝ) ≤
            C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
  have hballs : ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ContinuousPath.exitTime (Metric.ball x (n : ℝ)) b < ∞ := by
    simp only [ae_all_iff]
    exact fun n => Section6.ae_planarBrownianMotion_exitTime_ball_lt_top x n
  filter_upwards [planarBrownianMotion_shifted_dyadic_close_pairs_all_horizons x,
    hballs] with b hb hball D hD
  obtain ⟨R, hR⟩ := hD.subset_ball x
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsub : D ⊆ Metric.ball x (n : ℝ) := hR.trans (Metric.ball_subset_ball hn)
  have hfin : ContinuousPath.exitTime D b < ∞ :=
    lt_of_le_of_lt (ContinuousPath.exitTime_mono hsub b) (hball n)
  exact ⟨hfin, ENNReal.ofReal_toReal hfin.ne, hb _ ENNReal.toReal_nonneg⟩

end HarmonicBalls

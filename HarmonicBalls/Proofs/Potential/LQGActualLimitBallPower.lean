import HarmonicBalls.Proofs.Potential.LQGActualApproximantPower
import LatticeProb.LQG.CompactBallLimitPower

/-! # Compact-center power bounds for singular LQG measures

The common power bound for dyadic approximations passes to their vague limit.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The singular measure and its dyadic approximations have a common small-ball
power bound on every compact disk. -/
theorem IsWholePlaneGFF.ae_singular_limit_and_approximant_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
        μ ω (ball z s) ≤ ENNReal.ofReal (C * s ^ β) ∧
        ∀ k : ℕ, lqgApprox γ (fieldCircleAverage α (hcirc ω))
          (dyadicScale k) (ball z s) ≤ ENNReal.ofReal (C * s ^ β) := by
  filter_upwards [hh.ae_singular_approximant_ball_power_all_disks hγ hγ2 hαQ, hμ] with ω hb hlim R
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hb⟩ := hb R
  refine ⟨C, β, r₀, hC, hβ, hr₀, ?_⟩
  intro z hz s hs hsr
  refine ⟨?_, fun k => hb k z hz s hs hsr⟩
  have hvague : QuantumZipper.IsVagueLimitOn univ (fun k =>
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)) (μ ω) := by
    refine ⟨by simp, fun S hS _ => ?_, fun f hf hfc _ => hlim.tendsto_integral f hf hfc⟩
    let _ := hlim.isLocallyFiniteMeasure
    exact hS.measure_lt_top
  apply LatticeProb.LQG.measure_open_le_of_isVagueLimitOn hvague isOpen_ball isBounded_ball
  · refine ⟨z + (s + 1 : ℝ), ?_⟩
    simp only [mem_compl_iff, mem_ball, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ s + 1 by linarith), not_lt]
    linarith
  · intro k
    exact hb k z hz s hs hsr

end HarmonicBalls

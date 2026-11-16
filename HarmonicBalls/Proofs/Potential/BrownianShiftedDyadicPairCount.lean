import HarmonicBalls.Proofs.Potential.BrownianDyadicPairTransfer
import HarmonicBalls.Proofs.Potential.BrownianSharpLogOccupationEvent

/-! # Shifted dyadic Brownian pair counts

The sharp occupation and modulus estimates bound close pairs on every shifted grid.
-/

open MeasureTheory Set
open scoped NNReal

namespace HarmonicBalls

/-- At every positive dyadic scale and every shift, the number of ordered pairs
of shifted-grid times with nearby planar Brownian values has a cubic logarithmic bound. -/
theorem planarBrownianMotion_shifted_dyadic_close_pairs (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ,
        (sampledClosePairCount (fun t => b (Real.toNNReal t)) (shiftedDyadicIndices s k)
          (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ)) ((1 / 2 : ℝ) ^ k) : ℝ) ≤
            C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
  filter_upwards [planarBrownianMotion_ae_sqrt_dyadic_modulus x,
    planarBrownianMotion_uniform_ball_occupation_log_real_time x] with b hmod hocc
  obtain ⟨L, hL, hmod⟩ := hmod 1
  obtain ⟨A, hA, ε, hε, hocc⟩ := hocc
  have hmod' : ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |u - v| ≤ (1 / 4 : ℝ) ^ k →
      ‖b (Real.toNNReal u) - b (Real.toNNReal v)‖ ≤
        L * (1 / 2 : ℝ) ^ k * Real.sqrt k := by
    intro k hk u hu v hv huv
    apply hmod k hk (Real.toNNReal u) (Real.toNNReal v)
    · exact Real.toNNReal_le_one.mpr hu.2
    · exact Real.toNNReal_le_one.mpr hv.2
    · simpa [Real.coe_toNNReal', max_eq_left hu.1, max_eq_left hv.1] using huv
  obtain ⟨C, hC, hbound⟩ := shifted_dyadic_close_pairs_of_occupation
    (fun t => b (Real.toNNReal t)) L A (ε / 2) hL hA.le (by positivity) hmod'
    (by
      intro z r hr hrε
      exact hocc z r hr (by linarith))
  refine ⟨C + 1, by linarith, ?_⟩
  intro k hk s
  exact (hbound k hk s).trans (by gcongr; linarith)

end HarmonicBalls

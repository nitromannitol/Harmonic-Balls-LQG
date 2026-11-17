import HarmonicBalls.Proofs.Potential.LQGClockInnerAnnealedTail

/-! # Uniform dyadic inner expectation bounds

A summable sequence controls expected inner occupations at every smoothing scale.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- One summable sequence bounds the expected inner occupation at each dyadic
radius uniformly over positive smoothing radii at most one half. -/
theorem exists_summable_uniform_inner_inserted_expectation_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∃ B : ℕ → ℝ≥0∞, (∑' n, B n) < ∞ ∧ ∀ (n : ℕ) (ε : ℝ),
      0 < ε → ε ≤ 1/2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+1)}.indicator (fun z =>
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤ B n := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_inner_inserted_le hh x γ α p hq hqp hp
  let δ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδhalf (n : ℕ) : δ n ≤ 1 / 2 := by
    dsimp [δ]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have he : 0 < p - γ * α := sub_pos.mpr hqp
  refine ⟨fun n => ENNReal.ofReal ((δ n) ^ (p - γ * α)) * C, ?_, ?_⟩
  · rw [ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top _ hC
    exact (ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h)
      (fun n : ℕ => ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n) ^ (p - γ * α)))).trans_lt
        (tsum_dyadic_rpow_lt_top he)
  · intro n ε hε hεhalf
    have hn := hbound hε hεhalf (hδ n) (hδhalf n)
    rw [ENNReal.ofReal_rpow_of_nonneg (hδ n).le he.le] at hn
    exact hn

end HarmonicBalls

import HarmonicBalls.Proofs.Potential.LQGClockInnerProduct
import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation

/-! # Inner clock occupation along smoothing sequences

Quenched summability of inserted clock occupations for countable families of smoothing sequences.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- For an arbitrary deterministic smoothing sequence, the inner occupations at dyadic
cutoff radii are summable almost surely under the product law. -/
theorem ae_tsum_inner_inserted_sequence_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hεhalf : ∀ n, ε n ≤ 1 / 2) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (∑' n : ℕ, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n) z))
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
      ({z : ℂ | ‖z‖ < δ n}.indicator (fun z => (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n) z)) (q.2 s.toNNReal))
  have hF (n : ℕ) : AEMeasurable (F n) (P.prod (planarBrownianMotion x)) :=
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) (hε n) γ α (δ n) 0 1
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
    have hn := hbound (hε n) (hεhalf n) (hδ n) (hδhalf n)
    rw [ENNReal.ofReal_rpow_of_nonneg (hδ n).le he.le] at hn
    exact hn
  exact ae_lt_top' (AEMeasurable.tsum hF) hint.ne

/-- One field event works for a countable family of deterministic smoothing sequences;
for each sequence the occupation series is finite for almost every Brownian path. -/
theorem ae_ae_tsum_inner_inserted_sequences_lt_top
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ι → ℕ → ℝ) (hε : ∀ i n, 0 < ε i n)
    (hεhalf : ∀ i n, ε i n ≤ 1 / 2)
    (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∀ᵐ ω ∂P, ∀ i, ∀ᵐ b ∂planarBrownianMotion x,
      (∑' n : ℕ, ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          (ε i n) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε i n) z))
              (b s.toNNReal))) < ∞ := by
  apply ae_all_iff.mpr
  intro i
  exact Measure.ae_ae_of_ae_prod
    (ae_tsum_inner_inserted_sequence_lt_top hh x γ α p (ε i) (hε i) (hεhalf i) hq hqp hp)

end HarmonicBalls

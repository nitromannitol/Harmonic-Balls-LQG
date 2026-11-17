import HarmonicBalls.Proofs.Potential.LQGClockInnerSequences

/-! # Annealed tails of inner clock occupations

The expected tail of diagonal inner occupations vanishes for any deterministic
sequence of smoothing scales.
-/

open MeasureTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The sum of the expected inner occupations at dyadic radii is finite,
uniformly over deterministic choices of smoothing scale. -/
theorem lintegral_tsum_inner_inserted_sequence_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hεhalf : ∀ n, ε n ≤ 1 / 2) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    (∫⁻ q : Ω × ContinuousPath ℂ, ∑' n : ℕ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n) z))
              (q.2 s.toNNReal))) ∂(P.prod (planarBrownianMotion x))) < ∞ := by
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
  change (∫⁻ q, ∑' n, F n q ∂(P.prod (planarBrownianMotion x))) < ∞
  rw [lintegral_tsum hF]
  refine (ENNReal.tsum_le_tsum fun n => ?_).trans_lt hsum
  have hn := hbound (hε n) (hεhalf n) (hδ n) (hδhalf n)
  rw [ENNReal.ofReal_rpow_of_nonneg (hδ n).le he.le] at hn
  exact hn

/-- Expected tails of diagonal inner occupations tend to zero. -/
theorem tendsto_lintegral_tsum_inner_inserted_tail_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hεhalf : ∀ n, ε n ≤ 1 / 2) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    Tendsto (fun k : ℕ => ∫⁻ q : Ω × ContinuousPath ℂ,
      ∑' n : {n : ℕ // n ∉ Finset.range k}, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n.1 + 1)}.indicator (fun z =>
          (ε n.1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n.1) z))
              (q.2 s.toNNReal))) ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  let μ := P.prod (planarBrownianMotion x)
  let F (n : ℕ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
        (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n) z)) (q.2 s.toNNReal))
  have hF (n : ℕ) : AEMeasurable (F n) μ :=
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) (hε n) γ α _ 0 1
  have hsum : (∑' n, ∫⁻ q, F n q ∂μ) ≠ ∞ := by
    rw [← lintegral_tsum hF]
    exact (lintegral_tsum_inner_inserted_sequence_lt_top hh x γ α p ε hε hεhalf hq hqp hp).ne
  have ht := (ENNReal.tendsto_tsum_compl_atTop_zero hsum).comp tendsto_finset_range
  convert ht using 1
  funext k
  exact lintegral_tsum (fun n : {n : ℕ // n ∉ Finset.range k} => hF n.1)

end HarmonicBalls

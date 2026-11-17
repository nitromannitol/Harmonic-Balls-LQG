import HarmonicBalls.Proofs.Potential.LQGClockInnerLiminf
import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation

/-! # Lower limits at dyadic inner cutoffs

Expected inner-occupation bounds give summable lower limits as the cutoff shrinks.
-/

open MeasureTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- For a fixed smoothing sequence, the lower limits of actual inner
occupations are summable along dyadic cutoff radii under the product law. -/
theorem ae_tsum_liminf_inner_inserted_dyadic_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i)
    (hεhalf : ∀ i, ε i ≤ 1/2)
    (hq : 0 < γ*α) (hqp : γ*α < p) (hp : p < 2) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (∑' n : ℕ, liminf (fun i : ℕ =>
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+1)}.indicator (fun z =>
            (ε i)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε i) z))
            (q.2 s.toNNReal))) atTop) < ∞ := by
  let δ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδhalf (n : ℕ) : δ n ≤ 1/2 := by
    dsimp [δ]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let F (n : ℕ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
    liminf (fun i : ℕ => ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ n}.indicator (fun z => (ε i)^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε i) z)) (q.2 s.toNNReal))) atTop
  have hF (n : ℕ) : AEMeasurable (F n) (P.prod (planarBrownianMotion x)) :=
    AEMeasurable.liminf (fun i => aemeasurable_inner_inserted_clock_cell
      hh (planarBrownianMotion x) (hε i) γ α (δ n) 0 1)
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_liminf_brownian_inner_inserted_le hh x γ α p hq hqp hp
  have he : 0 < p - γ*α := sub_pos.mpr hqp
  have hsum : (∑' n : ℕ, ENNReal.ofReal ((δ n)^(p-γ*α)) * C) < ∞ := by
    rw [ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top _ hC
    exact (ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h)
      (fun n : ℕ => ENNReal.ofReal (((2 : ℝ)⁻¹ ^ n)^(p-γ*α)))).trans_lt
        (tsum_dyadic_rpow_lt_top he)
  have hint : (∫⁻ q, ∑' n, F n q ∂(P.prod (planarBrownianMotion x))) < ∞ := by
    rw [lintegral_tsum hF]
    refine (ENNReal.tsum_le_tsum fun n => ?_).trans_lt hsum
    have hn := hbound ε hε hεhalf (hδ n) (hδhalf n)
    rw [ENNReal.ofReal_rpow_of_nonneg (hδ n).le he.le] at hn
    exact hn
  exact ae_lt_top' (AEMeasurable.tsum hF) hint.ne

/-- The lower limits of actual inner occupations tend to zero as the dyadic
cutoff radius shrinks, almost surely under the product law. -/
theorem ae_tendsto_liminf_inner_inserted_dyadic_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i)
    (hεhalf : ∀ i, ε i ≤ 1/2)
    (hq : 0 < γ*α) (hqp : γ*α < p) (hp : p < 2) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      Tendsto (fun n : ℕ => liminf (fun i : ℕ =>
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+1)}.indicator (fun z =>
            (ε i)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε i) z))
            (q.2 s.toNNReal))) atTop) atTop (𝓝 0) := by
  filter_upwards [ae_tsum_liminf_inner_inserted_dyadic_lt_top
    hh x γ α p ε hε hεhalf hq hqp hp] with q hqsum
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hqsum.ne

/-- The dyadic-cutoff lower limits tend to zero for almost every field and
then almost every Brownian path. -/
theorem ae_field_ae_tendsto_liminf_inner_inserted_dyadic_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i)
    (hεhalf : ∀ i, ε i ≤ 1/2)
    (hq : 0 < γ*α) (hqp : γ*α < p) (hp : p < 2) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      Tendsto (fun n : ℕ => liminf (fun i : ℕ =>
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+1)}.indicator (fun z =>
            (ε i)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε i) z))
            (b s.toNNReal))) atTop) atTop (𝓝 0) :=
  Measure.ae_ae_of_ae_prod
    (ae_tendsto_liminf_inner_inserted_dyadic_zero hh x γ α p ε hε hεhalf hq hqp hp)


end HarmonicBalls

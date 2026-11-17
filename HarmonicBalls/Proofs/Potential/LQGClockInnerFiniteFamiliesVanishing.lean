import HarmonicBalls.Proofs.Potential.LQGClockInnerFiniteFamilies

/-! # Vanishing inner clock occupation for finite smoothing families

The sum over each finite family tends to zero at the corresponding dyadic radius.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The sum of inner occupations over each finite smoothing family tends to zero. -/
theorem ae_tendsto_inner_inserted_finite_families_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (N : ℕ → ℕ) (ε : ℕ → ℕ → ℝ)
    (hε : ∀ n i, i < N n → 0 < ε n i)
    (hεhalf : ∀ n i, i < N n → ε n i ≤ 1 / 2)
    (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2)
    (hsum : (∑' n : ℕ, (N n : ℝ≥0∞) *
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n + 1)) ^ (p - γ * α))) < ∞) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (N n), ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          (ε n i) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n i) z))
              (q.2 s.toNNReal))) Filter.atTop (nhds 0) := by
  filter_upwards [ae_tsum_inner_inserted_finite_families_lt_top hh x γ α p N ε
    hε hεhalf hq hqp hp hsum] with q hqsum
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hqsum.ne

/-- The finite-family convergence holds for almost every field and Brownian path. -/
theorem ae_ae_tendsto_inner_inserted_finite_families_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (N : ℕ → ℕ) (ε : ℕ → ℕ → ℝ)
    (hε : ∀ n i, i < N n → 0 < ε n i)
    (hεhalf : ∀ n i, i < N n → ε n i ≤ 1 / 2)
    (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2)
    (hsum : (∑' n : ℕ, (N n : ℝ≥0∞) *
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n + 1)) ^ (p - γ * α))) < ∞) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (N n), ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          (ε n i) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n i) z))
              (b s.toNNReal))) Filter.atTop (nhds 0) := by
  filter_upwards [ae_ae_tsum_inner_inserted_finite_families_lt_top hh x γ α p N ε
    hε hεhalf hq hqp hp hsum] with ω hω
  filter_upwards [hω] with b hb
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hb.ne

end HarmonicBalls

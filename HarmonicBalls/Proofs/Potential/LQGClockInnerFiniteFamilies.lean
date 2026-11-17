import HarmonicBalls.Proofs.Potential.LQGClockInnerSequences

/-! # Inner clock occupation for finite smoothing families

Summability for finite families with a summable cardinality-weighted bound.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Finite smoothing families have summable inner occupations under a summable
cardinality-weighted dyadic bound. -/
theorem ae_tsum_inner_inserted_finite_families_lt_top
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
      (∑' n : ℕ, ∑ i ∈ Finset.range (N n), ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          (ε n i) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n i) z))
              (q.2 s.toNNReal))) < ∞ := by
  let δ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδhalf (n : ℕ) : δ n ≤ 1 / 2 := by
    dsimp [δ]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let F (n i : ℕ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ n}.indicator (fun z => (ε n i) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε n i) z)) (q.2 s.toNNReal))
  have hF (n i : ℕ) (hi : i ∈ Finset.range (N n)) :
      AEMeasurable (F n i) (P.prod (planarBrownianMotion x)) :=
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x)
      (hε n i (Finset.mem_range.mp hi)) γ α (δ n) 0 1
  have hS (n : ℕ) : AEMeasurable (fun q => ∑ i ∈ Finset.range (N n), F n i q)
      (P.prod (planarBrownianMotion x)) := Finset.aemeasurable_fun_sum _ (hF n)
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_inner_inserted_le hh x γ α p hq hqp hp
  have he : 0 < p - γ * α := sub_pos.mpr hqp
  have hint : (∫⁻ q, ∑' n, ∑ i ∈ Finset.range (N n), F n i q
      ∂(P.prod (planarBrownianMotion x))) < ∞ := by
    rw [lintegral_tsum hS]
    calc
      _ ≤ ∑' n, ((N n : ℝ≥0∞) * ENNReal.ofReal ((δ n) ^ (p - γ * α))) * C := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [lintegral_finsetSum' _ (hF n)]
        calc
          _ ≤ ∑ _i ∈ Finset.range (N n), ENNReal.ofReal ((δ n) ^ (p - γ * α)) * C := by
            apply Finset.sum_le_sum
            intro i hi
            have hn := hbound (hε n i (Finset.mem_range.mp hi))
              (hεhalf n i (Finset.mem_range.mp hi)) (hδ n) (hδhalf n)
            rw [ENNReal.ofReal_rpow_of_nonneg (hδ n).le he.le] at hn
            exact hn
          _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = (∑' n, (N n : ℝ≥0∞) * ENNReal.ofReal ((δ n) ^ (p - γ * α))) * C :=
        ENNReal.tsum_mul_right
      _ < ∞ := ENNReal.mul_lt_top hsum hC
  exact ae_lt_top' (AEMeasurable.tsum hS) hint.ne

/-- The same finite-family series is finite for almost every field and Brownian path. -/
theorem ae_ae_tsum_inner_inserted_finite_families_lt_top
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
      (∑' n : ℕ, ∑ i ∈ Finset.range (N n), ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
          (ε n i) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n i) z))
              (b s.toNNReal))) < ∞ :=
  Measure.ae_ae_of_ae_prod
    (ae_tsum_inner_inserted_finite_families_lt_top hh x γ α p N ε hε hεhalf hq hqp hp hsum)

end HarmonicBalls

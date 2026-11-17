import HarmonicBalls.Proofs.Potential.LQGClockInnerFiniteFamilies

/-! # Expected coarse-scale inner occupations

The expected sum over coarse dyadic smoothing scales tends to zero.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem tsum_linear_dyadic_rpow_lt_top {p : ℝ} (hp : 0 < p) :
    (∑' n : ℕ, (n + 1 : ℕ) *
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n + 1)) ^ p)) < ∞ := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ p
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hs1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖r‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]))
  have hs0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n * r) := by
    convert (hs1.add hs0).mul_right r using 1
    ext n
    ring
  have heq (n : ℕ) : (↑(n + 1) : ℝ≥0∞) *
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n + 1)) ^ p) =
      ENNReal.ofReal (((n : ℝ) + 1) * r ^ n * r) := by
    have hpow : ((2 : ℝ)⁻¹ ^ (n + 1)) ^ p = r ^ n * r := by
      dsimp [r]
      rw [← Real.rpow_natCast_mul (by norm_num) (n + 1) p,
        show ((n + 1 : ℕ) : ℝ) * p = p * ((n + 1 : ℕ) : ℝ) by ring,
        Real.rpow_mul_natCast (by norm_num), pow_succ]
    rw [hpow, ENNReal.ofReal_mul (show 0 ≤ ((n : ℝ) + 1) * r ^ n by positivity),
      ENNReal.ofReal_mul (show 0 ≤ (n : ℝ) + 1 by positivity), ENNReal.ofReal_pow hr0,
      show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, ENNReal.ofReal_natCast, mul_assoc]
    rw [ENNReal.ofReal_mul (pow_nonneg hr0 _), ENNReal.ofReal_pow hr0]
  simp_rw [heq]
  exact hs.tsum_ofReal_lt_top

/-- For each fixed start, the expected sum of inner occupations over smoothing
scales at least the cutoff tends to zero. -/
theorem tendsto_lintegral_sum_inner_inserted_coarse_dyadic_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (hq : 0 < γ*α) (hqp : γ*α < p) (hp : p < 2) :
    Tendsto (fun n : ℕ => ∫⁻ q : Ω × ContinuousPath ℂ,
      (∑ i ∈ Finset.range (n+1), ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+1)}.indicator (fun z =>
          ((2 : ℝ)⁻¹ ^ (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ((2 : ℝ)⁻¹ ^ (i+1)) z))
              (q.2 s.toNNReal))) ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let d : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdhalf (n : ℕ) : d n ≤ 1/2 := by
    dsimp [d]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let F (n i : ℕ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d i)^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z)) (q.2 s.toNNReal))
  have hF (n i : ℕ) : AEMeasurable (F n i) (P.prod (planarBrownianMotion x)) :=
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) (hd i) γ α (d n) 0 1
  obtain ⟨C, hC, hbound⟩ := exists_lintegral_prod_brownian_inner_inserted_le hh x γ α p hq hqp hp
  have he : 0 < p - γ*α := sub_pos.mpr hqp
  have hs : (∑' n : ℕ, (↑(n+1) : ℝ≥0∞) * ENNReal.ofReal ((d n)^(p-γ*α))) < ∞ :=
    tsum_linear_dyadic_rpow_lt_top he
  have hint : (∑' n : ℕ, ∫⁻ q, ∑ i ∈ Finset.range (n+1), F n i q
      ∂(P.prod (planarBrownianMotion x))) < ∞ := by
    calc
      _ ≤ ∑' n : ℕ, ((↑(n+1) : ℝ≥0∞) * ENNReal.ofReal ((d n)^(p-γ*α))) * C := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [lintegral_finsetSum' _ (fun i _ => hF n i)]
        calc
          _ ≤ ∑ _i ∈ Finset.range (n+1), ENNReal.ofReal ((d n)^(p-γ*α)) * C := by
            apply Finset.sum_le_sum
            intro i hi
            have hn := hbound (hd i) (hdhalf i) (hd n) (hdhalf n)
            rw [ENNReal.ofReal_rpow_of_nonneg (hd n).le he.le] at hn
            exact hn
          _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = (∑' n : ℕ, (↑(n+1) : ℝ≥0∞) * ENNReal.ofReal ((d n)^(p-γ*α))) * C :=
        ENNReal.tsum_mul_right
      _ < ∞ := ENNReal.mul_lt_top hs hC
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hint.ne
  simpa only [F, d] using ht

end HarmonicBalls

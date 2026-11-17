import HarmonicBalls.Proofs.Potential.LQGClockInnerFiniteFamiliesVanishing

/-! # Inner clock occupation at coarse dyadic scales

The occupations at all dyadic smoothing scales no finer than the cutoff vanish together.
-/

open MeasureTheory MarkovProcess Set
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

/-- The sum of actual inner occupations over dyadic smoothing scales at least the cutoff
converges to zero for almost every field and Brownian path. -/
theorem ae_ae_tendsto_inner_inserted_coarse_dyadic_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n + 1)}.indicator (fun z =>
            ((2 : ℝ)⁻¹ ^ (i + 1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ((2 : ℝ)⁻¹ ^ (i + 1)) z))
                (b s.toNNReal))) Filter.atTop (nhds 0) := by
  apply ae_ae_tendsto_inner_inserted_finite_families_zero hh x γ α p
    (fun n => n + 1) (fun _ i => (2 : ℝ)⁻¹ ^ (i + 1))
  · intro n i hi
    positivity
  · intro n i hi
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  · exact hq
  · exact hqp
  · exact hp
  · exact tsum_linear_dyadic_rpow_lt_top (sub_pos.mpr hqp)

end HarmonicBalls

import HarmonicBalls.Proofs.Potential.BrownianDyadicPairCount
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Dyadic Brownian modulus

Almost sure dyadic oscillation estimates for planar Brownian motion.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The dyadic time scale. -/
noncomputable def brownianDyadicTime (k : ℕ) : ℝ≥0 := (1 / 4) ^ k

/-- A square-root logarithmic oscillation threshold at a dyadic time scale. -/
noncomputable def brownianDyadicThreshold (k : ℕ) : ℝ :=
  64 * Real.sqrt (((k : ℝ) + 1) * ((1 / 4 : ℝ) ^ k))

/-- The threshold at each dyadic scale is positive. -/
theorem brownianDyadicThreshold_pos (k : ℕ) : 0 < brownianDyadicThreshold k := by
  unfold brownianDyadicThreshold
  positivity

/-- The Gaussian exponent in the fixed-scale bound simplifies on the dyadic sequence. -/
theorem brownianDyadic_exponent (k : ℕ) :
    -(((brownianDyadicThreshold k / 2) / 2) ^ 2 /
      (32 * (2 * (brownianDyadicTime k : ℝ)))) = -4 * ((k : ℝ) + 1) := by
  have hsq : (Real.sqrt (((k : ℝ) + 1) * ((1 / 4 : ℝ) ^ k))) ^ 2 =
      ((k : ℝ) + 1) * ((1 / 4 : ℝ) ^ k) := Real.sq_sqrt (by positivity)
  have hp : (1 / 4 : ℝ) ^ k ≠ 0 := ne_of_gt (by positivity)
  simp only [brownianDyadicThreshold, brownianDyadicTime, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  field_simp
  nlinarith

/-- The fixed-scale tail on the dyadic sequence is bounded by a geometric term. -/
theorem planarBrownianMotion_dyadic_modulus_tail (x : ℂ) (N k : ℕ) :
    planarBrownianMotion x {ω | ∃ s t : ℝ≥0, s ≤ N ∧ t ≤ N ∧
      |(s : ℝ) - t| ≤ brownianDyadicTime k ∧
      brownianDyadicThreshold k ≤ ‖ω s - ω t‖} ≤
    ENNReal.ofReal (8 * (N + 1) * (4 * Real.exp (-4)) ^ k) := by
  have hp : 0 < brownianDyadicTime k := by
    simp only [brownianDyadicTime]
    positivity
  have ht := planarBrownianMotion_modulus_tail x (N : ℝ≥0)
    (brownianDyadicTime k) hp (brownianDyadicThreshold_pos k)
  rw [brownianDyadic_exponent] at ht
  have hceil : ⌈((N : ℝ≥0) : ℝ) / (brownianDyadicTime k : ℝ)⌉₊ = N * 4 ^ k := by
    have heq : ((N : ℝ≥0) : ℝ) / (brownianDyadicTime k : ℝ) = (N * 4 ^ k : ℕ) := by
      simp only [brownianDyadicTime, NNReal.coe_pow, NNReal.coe_div,
        NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast, Nat.cast_mul, Nat.cast_pow]
      simp [div_eq_mul_inv]
    rw [heq, Nat.ceil_natCast]
  rw [hceil] at ht
  refine ht.trans ?_
  have hn : (((N * 4 ^ k + 1 : ℕ) : ℝ)) ≤ (N + 1) * 4 ^ k := by
    push_cast
    have : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have he : Real.exp (-4 * ((k : ℝ) + 1)) ≤ Real.exp (-4 * k) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow : (4 * Real.exp (-4)) ^ k = 4 ^ k * Real.exp (-4 * k) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  rw [hpow]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat (n := 4),
    ← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    2 * (((N * 4 ^ k + 1 : ℕ) : ℝ) * (4 * Real.exp (-4 * ((k : ℝ) + 1))))
        ≤ 2 * ((N + 1) * 4 ^ k * (4 * Real.exp (-4 * k))) := by gcongr
    _ = 8 * (N + 1) * (4 ^ k * Real.exp (-4 * k)) := by ring

/-- All bounded time intervals satisfy the dyadic bound at sufficiently fine scales. -/
theorem planarBrownianMotion_ae_eventually_dyadic_modulus (x : ℂ) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ∀ N : ℕ, ∀ᶠ k in atTop,
      ∀ s t : ℝ≥0, s ≤ N → t ≤ N →
        |(s : ℝ) - t| ≤ brownianDyadicTime k →
        ‖ω s - ω t‖ < brownianDyadicThreshold k := by
  apply ae_all_iff.mpr
  intro N
  let E : ℕ → Set (ContinuousPath ℂ) := fun k =>
    {ω | ∃ s t : ℝ≥0, s ≤ N ∧ t ≤ N ∧
      |(s : ℝ) - t| ≤ brownianDyadicTime k ∧
      brownianDyadicThreshold k ≤ ‖ω s - ω t‖}
  have hr0 : 0 ≤ 4 * Real.exp (-4) := by positivity
  have hr1 : 4 * Real.exp (-4) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos 4)]
    have h := Real.add_one_lt_exp (show (4 : ℝ) ≠ 0 by norm_num)
    linarith
  have hs : Summable (fun k : ℕ => 8 * (N + 1 : ℝ) * (4 * Real.exp (-4)) ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsum : (∑' k, planarBrownianMotion x (E k)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' k,
      8 * (N + 1 : ℝ) * (4 * Real.exp (-4)) ^ k)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
    exact ENNReal.tsum_le_tsum (fun k => planarBrownianMotion_dyadic_modulus_tail x N k)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with k hk s t hs ht hst
  exact lt_of_not_ge (fun h => hk ⟨s, t, hs, ht, hst, h⟩)

/-- On one event, every bounded time interval has a dyadic square-root modulus. -/
theorem planarBrownianMotion_ae_dyadic_modulus (x : ℂ) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ∀ T : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
        |(s : ℝ) - t| ≤ brownianDyadicTime k →
        ‖ω s - ω t‖ ≤ C * brownianDyadicThreshold k := by
  filter_upwards [planarBrownianMotion_ae_eventually_dyadic_modulus x] with ω hω T
  let N : ℕ := ⌈T⌉₊
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hω N)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (N : ℝ≥0))).exists_bound_of_continuousOn
    ω.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (ω 0)).trans (hM 0 ⟨zero_le, zero_le⟩)
  let C : ℝ := 1 + ∑ k ∈ Finset.range n₀, 2 * M / brownianDyadicThreshold k
  have hterm : ∀ k : ℕ, 0 ≤ 2 * M / brownianDyadicThreshold k := by
    intro k
    exact div_nonneg (mul_nonneg (by norm_num) hM0) (brownianDyadicThreshold_pos k).le
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (s := Finset.range n₀) (fun k _ => hterm k)]
  refine ⟨C, by linarith, ?_⟩
  intro k s t hs ht hst
  have hsN : s ≤ (N : ℝ≥0) := hs.trans (Nat.le_ceil T)
  have htN : t ≤ (N : ℝ≥0) := ht.trans (Nat.le_ceil T)
  by_cases hk : n₀ ≤ k
  · exact (hn₀ k hk s t hsN htN hst).le.trans
      (by nlinarith [brownianDyadicThreshold_pos k])
  · have hmem : k ∈ Finset.range n₀ := Finset.mem_range.mpr (by omega)
    have hle : 2 * M / brownianDyadicThreshold k ≤ C := by
      dsimp [C]
      have h := Finset.single_le_sum (fun j _ => hterm j) hmem
      linarith
    have hden := brownianDyadicThreshold_pos k
    have hsM : ‖ω s‖ ≤ M := hM s ⟨zero_le, hsN⟩
    have htM : ‖ω t‖ ≤ M := hM t ⟨zero_le, htN⟩
    calc
      ‖ω s - ω t‖ ≤ ‖ω s‖ + ‖ω t‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
      _ ≤ C * brownianDyadicThreshold k := (div_le_iff₀ hden).mp hle

/-- The dyadic threshold has the usual square-root logarithmic form. -/
theorem brownianDyadicThreshold_le (k : ℕ) (hk : 1 ≤ k) :
    brownianDyadicThreshold k ≤ 128 * (1 / 2 : ℝ) ^ k * Real.sqrt k := by
  have hp : (1 / 4 : ℝ) ^ k = ((1 / 2 : ℝ) ^ k) ^ 2 := by
    calc
      (1 / 4 : ℝ) ^ k = ((1 / 2 : ℝ) ^ 2) ^ k := by norm_num
      _ = ((1 / 2 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt k := by
    calc
      Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt (4 * k) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt k := by rw [Real.sqrt_mul (by norm_num)]; norm_num
  rw [brownianDyadicThreshold, hp, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) k]

/-- Planar Brownian motion has the square-root logarithmic modulus at every positive
 dyadic scale, simultaneously on every bounded time interval. -/
theorem planarBrownianMotion_ae_sqrt_dyadic_modulus (x : ℂ) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ∀ T : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
        |(s : ℝ) - t| ≤ (1 / 4 : ℝ) ^ k →
        ‖ω s - ω t‖ ≤ C * (1 / 2 : ℝ) ^ k * Real.sqrt k := by
  filter_upwards [planarBrownianMotion_ae_dyadic_modulus x] with ω hω T
  obtain ⟨C, hC, hbound⟩ := hω T
  refine ⟨128 * C, by positivity, ?_⟩
  intro k hk s t hs ht hst
  have hst' : |(s : ℝ) - t| ≤ brownianDyadicTime k := by
    simpa [brownianDyadicTime] using hst
  calc
    ‖ω s - ω t‖ ≤ C * brownianDyadicThreshold k := hbound k s t hs ht hst'
    _ ≤ C * (128 * (1 / 2 : ℝ) ^ k * Real.sqrt k) :=
      mul_le_mul_of_nonneg_left (brownianDyadicThreshold_le k hk) hC
    _ = (128 * C) * (1 / 2 : ℝ) ^ k * Real.sqrt k := by ring

end HarmonicBalls

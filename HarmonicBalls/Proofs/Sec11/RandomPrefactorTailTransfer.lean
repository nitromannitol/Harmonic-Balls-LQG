import HarmonicBalls.Proofs.Sec11.DyadicTailPrefactor

/-! # Random prefactors in dyadic tail estimates

The normalized tail is an explicit hypothesis. This result does not establish
an LQG metric source bridge. The imported Section 8 development uses Leonardo
Bonanno's LatticeProb formalization. -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- A positive moment gives a dyadic Markov bound for a nonnegative prefactor. -/
theorem measure_dyadic_prefactor_gt_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → ℝ)
    (hA : ∀ ω, 0 ≤ A ω) (q δ : ℝ) (hq : 0 < q)
    (hint : Integrable (fun ω => (A ω) ^ q) P) (n : ℕ) :
    P {ω | (2 : ℝ) ^ (δ * n) < A ω} ≤
      ENNReal.ofReal ((∫ ω, (A ω) ^ q ∂P) * (1 / 2 : ℝ) ^ ((δ * q) * n)) := by
  let m : ℝ := ∫ ω, (A ω) ^ q ∂P
  have hm : 0 ≤ m := integral_nonneg fun ω => Real.rpow_nonneg (hA ω) _
  have ht : 0 < (2 : ℝ) ^ ((δ * n) * q) := Real.rpow_pos_of_pos (by norm_num) _
  have hmarkov := meas_ge_le_lintegral_div hint.aemeasurable.ennreal_ofReal
    ((ENNReal.ofReal_pos.mpr ht).ne') ENNReal.ofReal_ne_top
  have hsubset : {ω | (2 : ℝ) ^ (δ * n) < A ω} ⊆
      {ω | ENNReal.ofReal ((2 : ℝ) ^ ((δ * n) * q)) ≤
        ENNReal.ofReal ((A ω) ^ q)} := by
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hω.le hq.le
  calc
    _ ≤ P {ω | ENNReal.ofReal ((2 : ℝ) ^ ((δ * n) * q)) ≤
        ENNReal.ofReal ((A ω) ^ q)} := measure_mono hsubset
    _ ≤ (∫⁻ ω, ENNReal.ofReal ((A ω) ^ q) ∂P) /
        ENNReal.ofReal ((2 : ℝ) ^ ((δ * n) * q)) := hmarkov
    _ = ENNReal.ofReal (m / (2 : ℝ) ^ ((δ * n) * q)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun ω => Real.rpow_nonneg (hA ω) _),
        ENNReal.ofReal_div_of_pos ht]
    _ = _ := by
      congr 1
      rw [div_eq_mul_inv, ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [one_div]
      congr 2
      ring

/-- A joint-law tail transfer with no independence assumption. The normalized
uniform tail is a hypothesis; the conclusion holds at all sufficiently fine
scales with any prescribed smaller positive exponent. -/
theorem dyadic_product_tail_of_all_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → ℝ)
    (T : ∀ n : ℕ, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ)
    (b : ℕ → ℝ) (δ p₀ p C : ℝ)
    (hA : ∀ ω, 0 ≤ A ω) (hT : ∀ n i ω, 0 ≤ T n i ω)
    (hδ : 0 < δ) (hp : 0 < p) (hpp : p < p₀)
    (hC : 0 ≤ C)
    (hmom : ∀ q : ℝ, 0 < q → Integrable (fun ω => (A ω) ^ q) P)
    (htail : ∀ᶠ n in atTop, ∀ i, P {ω | b n < T n i ω} ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (p₀ * n))) :
    ∀ᶠ n in atTop, ∀ i, P {ω | b n * (2 : ℝ) ^ (δ * n) < A ω * T n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (p * n)) := by
  let q : ℝ := (p₀ + 1) / δ
  have hq : 0 < q := div_pos (by linarith) hδ
  have hqeq : δ * q = p₀ + 1 := by dsimp [q]; field_simp
  let m : ℝ := ∫ ω, (A ω) ^ q ∂P
  have hm : 0 ≤ m := integral_nonneg fun ω => Real.rpow_nonneg (hA ω) _
  have habsorb := dyadic_scaled_power_error_prefactor_eventually_le (m + C) 1 p₀ p
    (add_nonneg hm hC) (by norm_num) hp hpp (fun _ => 0) tendsto_const_nhds
  filter_upwards [htail, habsorb] with n hn ha
  intro i
  have hpow : (1 / 2 : ℝ) ^ ((δ * q) * n) ≤ (1 / 2 : ℝ) ^ (p₀ * n) := by
    apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    rw [hqeq]
    exact mul_le_mul_of_nonneg_right (by linarith : p₀ ≤ p₀ + 1) (Nat.cast_nonneg n)
  have hmarkov := measure_dyadic_prefactor_gt_le P A hA q δ hq (hmom q hq) n
  calc
    _ ≤ P ({ω | (2 : ℝ) ^ (δ * n) < A ω} ∪ {ω | b n < T n i ω}) := by
      apply measure_mono
      intro ω hω
      change b n * (2 : ℝ) ^ (δ * n) < A ω * T n i ω at hω
      by_contra hc
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hc
      have hmul := mul_le_mul hc.1 hc.2 (hT n i ω) (Real.rpow_nonneg (by norm_num) _)
      exact (not_lt_of_ge hmul) (by simpa only [mul_comm (b n)] using hω)
    _ ≤ P {ω | (2 : ℝ) ^ (δ * n) < A ω} + P {ω | b n < T n i ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (m * (1 / 2 : ℝ) ^ (p₀ * n)) +
        ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (p₀ * n)) := by
      gcongr
      · exact hmarkov.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hm))
      · exact hn i
    _ = ENNReal.ofReal ((m + C) * (1 / 2 : ℝ) ^ (p₀ * n)) := by
      rw [add_mul, ENNReal.ofReal_add (mul_nonneg hm (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simp only [one_mul, add_zero, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ha
      simpa only [mul_comm (n : ℝ) p₀] using ha)

/-- If the normalized exponent exceeds the planar square-count exponent,
one can retain an exponent above two after the random-prefactor transfer. -/
theorem exists_dyadic_product_tail_exponent_gt_two
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → ℝ)
    (T : ∀ n : ℕ, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ)
    (b : ℕ → ℝ) (δ p₀ C : ℝ)
    (hA : ∀ ω, 0 ≤ A ω) (hT : ∀ n i ω, 0 ≤ T n i ω)
    (hδ : 0 < δ) (hp₀ : 2 < p₀) (hC : 0 ≤ C)
    (hmom : ∀ q : ℝ, 0 < q → Integrable (fun ω => (A ω) ^ q) P)
    (htail : ∀ᶠ n in atTop, ∀ i, P {ω | b n < T n i ω} ≤
      ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (p₀ * n))) :
    ∃ p : ℝ, 2 < p ∧ p < p₀ ∧ ∀ᶠ n in atTop, ∀ i,
      P {ω | b n * (2 : ℝ) ^ (δ * n) < A ω * T n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (p * n)) := by
  let p := (2 + p₀) / 2
  have hp : 2 < p := by dsimp [p]; linarith
  have hpp : p < p₀ := by dsimp [p]; linarith
  exact ⟨p, hp, hpp, dyadic_product_tail_of_all_moments P A T b δ p₀ p C
    hA hT hδ (by linarith) hpp hC hmom htail⟩

/-- A dyadic power threshold still vanishes after multiplying by the
polynomial allowance, provided its original exponent is strictly larger. -/
theorem dyadic_threshold_mul_growth_eventually_lt
    (c s δ : ℝ) (hδs : δ < s) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (1 / 2 : ℝ) ^ (s * n) * (2 : ℝ) ^ (δ * n)) <
        ENNReal.ofReal a := by
  filter_upwards [dyadic_diameter_threshold_eventually_lt c (s - δ) (by linarith) a ha]
    with n hn
  have hid : (2 : ℝ) ^ (δ * n) = (1 / 2 : ℝ) ^ (-(δ * n)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  rw [hid, mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
  have hexp : s * (n : ℝ) + -(δ * n) = (s - δ) * n := by ring
  rw [hexp]
  exact hn

end HarmonicBalls

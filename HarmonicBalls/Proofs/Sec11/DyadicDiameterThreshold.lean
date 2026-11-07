import HarmonicBalls.Proofs.Sec11.DyadicIntermediateTailComparison

/-! # Vanishing thresholds for dyadic diameter estimates -/

namespace HarmonicBalls
open Filter Topology
open scoped ENNReal

/-- A fixed positive side-length factor and normalization constant do not
prevent a positive power of the dyadic mesh from tending to zero. -/
theorem dyadic_diameter_threshold_eventually_lt (C s : ℝ) (hs : 0 < s)
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (s * n)) <
      ENNReal.ofReal a := by
  have hq0 : 0 ≤ (1 / 2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) _
  have hq1 : (1 / 2 : ℝ) ^ s < 1 := by
    simpa using Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hs
  have ht : Tendsto (fun n : ℕ => C * ((1 / 2 : ℝ) ^ s) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have he : ∀ᶠ n : ℕ in atTop, C * ((1 / 2 : ℝ) ^ s) ^ n < a :=
    ht.eventually (Iio_mem_nhds ha)
  filter_upwards [he] with n hn
  apply (ENNReal.ofReal_lt_ofReal_iff ha).2
  simpa only [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast] using hn

/-- The actual intermediate-square side is `3L / (2 * 2^n)`; its
positive-power threshold vanishes even after a fixed normalization. -/
theorem intermediate_square_threshold_eventually_lt (c L s : ℝ) (hL : 0 < L)
    (hs : 0 < s) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) <
        ENNReal.ofReal a := by
  filter_upwards [dyadic_diameter_threshold_eventually_lt
    (c * (3 * L / 2) ^ s) s hs a ha] with n hn
  have hside : 3 * L / (2 * (2 : ℝ) ^ n) =
      (3 * L / 2) * (1 / 2 : ℝ) ^ n := by
    rw [div_pow]
    field_simp
    ring
  rw [hside, Real.mul_rpow (by positivity : 0 ≤ 3 * L / 2)
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simpa only [mul_assoc, mul_comm (n : ℝ) s] using hn

/-- A fixed change of side length can be absorbed into any smaller positive
power, uniformly along dyadic scales, even with a vanishing exponent error. -/
theorem dyadic_scaled_power_error_eventually_le
    (C p p' : ℝ) (hC : 0 < C) (hp' : 0 < p') (hpp : p' < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (C * (1 / 2 : ℝ) ^ n) ^ (p + e n) ≤
        (1 / 2 : ℝ) ^ (p' * n) := by
  let r : ℝ := (p + p') / 2
  have hpr : p' < r := by dsimp [r]; linarith
  have hrp : r < p := by dsimp [r]; linarith
  have hr : 0 < r := hp'.trans hpr
  have hnear : ∀ᶠ n in atTop, r < p + e n := by
    filter_upwards [(tendsto_order.1 he).1 (r - p) (by linarith)] with n hn
    linarith
  have hside : ∀ᶠ n : ℕ in atTop, C * (1 / 2 : ℝ) ^ n < 1 := by
    filter_upwards [dyadic_diameter_threshold_eventually_lt C 1 (by norm_num) 1
      (by norm_num)] with n hn
    have := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).1 hn
    simpa using this
  have hfactor : ∀ᶠ n : ℕ in atTop,
      C ^ r * (1 / 2 : ℝ) ^ ((r - p') * n) < 1 := by
    filter_upwards [dyadic_diameter_threshold_eventually_lt (C ^ r) (r - p')
      (by linarith) 1 (by norm_num)] with n hn
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).1 hn
  filter_upwards [hnear, hside, hfactor] with n hn hs hf
  have hbase : 0 < C * (1 / 2 : ℝ) ^ n := by positivity
  calc
    (C * (1 / 2 : ℝ) ^ n) ^ (p + e n) ≤
        (C * (1 / 2 : ℝ) ^ n) ^ r :=
      Real.rpow_le_rpow_of_exponent_ge hbase hs.le hn.le
    _ = (C ^ r * (1 / 2 : ℝ) ^ ((r - p') * n)) *
        (1 / 2 : ℝ) ^ (p' * n) := by
      rw [Real.mul_rpow hC.le (by positivity : 0 ≤ (1 / 2 : ℝ) ^ n),
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
      congr 2
      ring
    _ ≤ (1 / 2 : ℝ) ^ (p' * n) := by
      calc
        _ ≤ 1 * (1 / 2 : ℝ) ^ (p' * n) :=
          mul_le_mul_of_nonneg_right hf.le (Real.rpow_nonneg (by norm_num) _)
        _ = _ := one_mul _

#print axioms dyadic_scaled_power_error_eventually_le
#print axioms dyadic_diameter_threshold_eventually_lt
#print axioms intermediate_square_threshold_eventually_lt
end HarmonicBalls

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

#print axioms dyadic_diameter_threshold_eventually_lt
#print axioms intermediate_square_threshold_eventually_lt
end HarmonicBalls

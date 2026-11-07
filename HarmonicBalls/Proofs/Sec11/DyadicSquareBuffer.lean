import HarmonicBalls.Proofs.Sec11.DyadicClosedGridCover

/-! # Buffered dyadic square geometry -/

namespace HarmonicBalls
open Set Filter Topology

/-- All enlarged dyadic squares lie in a fixed rectangular buffer once their
side length is sufficiently small. -/
theorem complex_enlarged_dyadic_square_subset_buffer
    (a : ℂ) (L ε : ℝ) (hL : 0 < L) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      complexEnlargedGridSquare a (L / (2 : ℝ) ^ n) i ⊆
        closedSquare (a - ⟨ε, ε⟩) (L + 2 * ε) := by
  have ht : Tendsto (fun n : ℕ => L * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul L
  have he : ∀ᶠ n : ℕ in atTop, L / (2 : ℝ) ^ n < ε := by
    filter_upwards [ht.eventually (Iio_mem_nhds hε)] with n hn
    simpa only [mem_Iio, div_eq_mul_inv, inv_pow, one_div, one_mul] using hn
  filter_upwards [he] with n hn i z hz
  have hr : 0 < L / (2 : ℝ) ^ n := by positivity
  have hi1 : (i.1.val : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    have h : i.1.val + 1 ≤ 2 ^ n := i.1.isLt
    exact_mod_cast h
  have hi2 : (i.2.val : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    have h : i.2.val + 1 ≤ 2 ^ n := i.2.isLt
    exact_mod_cast h
  have hprod : (2 : ℝ) ^ n * (L / (2 : ℝ) ^ n) = L := by
    field_simp
  have hmul1 := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n - ((i.1.val : ℝ) + 1) by linarith) hr.le
  have hmul2 := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n - ((i.2.val : ℝ) + 1) by linarith) hr.le
  have hnon1 : 0 ≤ (i.1.val : ℝ) := Nat.cast_nonneg _
  have hnon2 : 0 ≤ (i.2.val : ℝ) := Nat.cast_nonneg _
  change ((i.1.val : ℝ) - 3 / 8) * (L / (2 : ℝ) ^ n) ≤ z.re - a.re ∧
    z.re - a.re ≤ ((i.1.val : ℝ) + 11 / 8) * (L / (2 : ℝ) ^ n) ∧
    ((i.2.val : ℝ) - 3 / 8) * (L / (2 : ℝ) ^ n) ≤ z.im - a.im ∧
    z.im - a.im ≤ ((i.2.val : ℝ) + 11 / 8) * (L / (2 : ℝ) ^ n) at hz
  simp only [closedSquare, Complex.mem_reProdIm, mem_Icc, Complex.sub_re,
    Complex.sub_im]
  rcases hz with ⟨h1, h2, h3, h4⟩
  constructor <;> [constructor <;> nlinarith; constructor <;> nlinarith]

#print axioms complex_enlarged_dyadic_square_subset_buffer
end HarmonicBalls

import HarmonicBalls.Defs.Geometry

/-!
# Proposition 11.9, dyadic squares inside an open set

FIRST-PASS NEW. The first line of the proof of `prop:mass-diam-gen` (corrected paper, line 3111): since `U` is open, there
are deterministic closed dyadic squares `S₁ ⊆ S₂ ⊆ U` with `S₁` contained in the interior of `S₂`. Here `S₂` is the
dyadic square of side `2⁻ⁿ` containing a point `x ∈ U`, with `2⁻ⁿ < r/2` for a ball `B(x, r) ⊆ U`, and `S₁` is the
dyadic square of side `2⁻ⁿ⁻²` in the middle of `S₂` (indices `4j+1`, `4k+1`).
-/

namespace HarmonicBalls

open Set

/-- Deterministic dyadic squares (paper line 3111): for an open `U` and `x ∈ U`, there are closed dyadic squares
`S₁ ⊆ interior S₂` and `S₂ ⊆ U`. -/
theorem exists_closedDyadicSquare_pair {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    ∃ S₁ S₂ : Set ℂ, IsClosedDyadicSquare S₁ ∧ IsClosedDyadicSquare S₂ ∧ S₁ ⊆ interior S₂ ∧ S₂ ⊆ U := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hr) (by norm_num : (1 / 2 : ℝ) < 1)
  set n : ℤ := (N : ℤ) with hn
  set s : ℝ := (2 : ℝ) ^ (-n) with hs
  have hs_eq : s = (1 / 2 : ℝ) ^ N := by
    rw [hs, hn, zpow_neg, zpow_natCast, one_div, inv_pow]
  have hs_pos : 0 < s := by rw [hs]; positivity
  have hs_lt : s < r / 2 := by rw [hs_eq]; exact hN
  set j : ℤ := ⌊x.re / s⌋ with hj
  set k : ℤ := ⌊x.im / s⌋ with hk
  have hxre : (j : ℝ) * s ≤ x.re ∧ x.re ≤ ((j : ℝ) + 1) * s := by
    have h1 : (j : ℝ) ≤ x.re / s := Int.floor_le _
    have h2 : x.re / s < (j : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · have := (le_div_iff₀ hs_pos).mp h1; linarith
    · have := (div_lt_iff₀ hs_pos).mp h2; linarith
  have hxim : (k : ℝ) * s ≤ x.im ∧ x.im ≤ ((k : ℝ) + 1) * s := by
    have h1 : (k : ℝ) ≤ x.im / s := Int.floor_le _
    have h2 : x.im / s < (k : ℝ) + 1 := Int.lt_floor_add_one _
    constructor
    · have := (le_div_iff₀ hs_pos).mp h1; linarith
    · have := (div_lt_iff₀ hs_pos).mp h2; linarith
  refine ⟨closedDyadicSquare (n + 2) (4 * j + 1) (4 * k + 1), closedDyadicSquare n j k,
    ⟨n + 2, 4 * j + 1, 4 * k + 1, rfl⟩, ⟨n, j, k, rfl⟩, ?_, ?_⟩
  · -- the middle subsquare lies in the open square
    have hq : (2 : ℝ) ^ (-(n + 2)) = s / 4 := by
      have h4 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
      rw [hs, show -(n + 2) = -n + (-2 : ℤ) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), h4]
      ring
    have hopen : IsOpen {z : ℂ | z.re ∈ Ioo ((j : ℝ) * s) (((j : ℝ) + 1) * s) ∧
        z.im ∈ Ioo ((k : ℝ) * s) (((k : ℝ) + 1) * s)} :=
      (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
    have hin : {z : ℂ | z.re ∈ Ioo ((j : ℝ) * s) (((j : ℝ) + 1) * s) ∧
        z.im ∈ Ioo ((k : ℝ) * s) (((k : ℝ) + 1) * s)} ⊆ closedDyadicSquare n j k := by
      rintro z ⟨h1, h2⟩
      unfold closedDyadicSquare
      rw [← hs]
      exact ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩
    intro z hz
    unfold closedDyadicSquare at hz
    obtain ⟨hre, him⟩ := hz
    rw [hq] at hre him
    push_cast at hre him
    apply interior_maximal hin hopen
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [hre.1, hre.2, him.1, him.2, hs_pos]
  · intro z hz
    unfold closedDyadicSquare at hz
    obtain ⟨hzre, hzim⟩ := hz
    rw [← hs] at hzre hzim
    have hre1 : |z.re - x.re| ≤ s := by
      rw [abs_le]; constructor <;> linarith [hzre.1, hzre.2, hxre.1, hxre.2]
    have him1 : |z.im - x.im| ≤ s := by
      rw [abs_le]; constructor <;> linarith [hzim.1, hzim.2, hxim.1, hxim.2]
    have hdist : ‖z - x‖ ≤ 2 * s := by
      have h := Complex.norm_le_abs_re_add_abs_im (z - x)
      simp only [Complex.sub_re, Complex.sub_im] at h
      linarith
    exact hball (by rw [Metric.mem_ball, dist_eq_norm]; linarith)

end HarmonicBalls

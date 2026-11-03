import HarmonicBalls.Draft.Section6

/-!
# Lemma 6.12: the shell decomposition

Proof of `ShellDecompositionStmt` (lemma:shell-decomposition, lines 1636-1672 of
paper/lqg_harmonic_ball-corrected.tex). The widths are `l_j = ρ 2^{-50} r^j` with `r = 2^{-1/4} ≤ 6/7`
(`shellWidth_eq`, `shellRatio_le`), so `∑_j 32 l_j ≤ 224 · 2^{-50} ρ` and every radius `d_j` lies in
`[3ρ/4 - 224 · 2^{-50} ρ, 3ρ/4]` (`shellRadius_lower`, `shellRadius_le`). A point of `S_j + B_{8 l_j}` is at
distance `< 9 l_j` from the circle `∂B_{d_j}(x₀)` (`abs_dist_sub_lt_of_mem_add`); consecutive radii differ by
`32 l_j` (`shellRadius_le_sub`), which separates the shells; and `8 ε_j^{1/2} ρ ≤ 7 l_j` for `N₀ ≥ 200`
(`eight_sqrt_shellScale_mul_le`). The proof is deterministic and elementary.
-/

namespace HarmonicBalls

open Metric Set
open scoped Pointwise

namespace Section6

/-- The ratio `r = 2^{-1/4}` of consecutive shell widths. -/
noncomputable def shellRatio : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ))

theorem shellRatio_pos : 0 < shellRatio := Real.rpow_pos_of_pos (by norm_num) _

theorem shellRatio_pow_four : shellRatio ^ 4 = 1 / 2 := by
  rw [shellRatio, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 4 : ℝ))) 4,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show -(1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-- `2^{-1/4} ≤ 6/7`, since `(6/7)^4 > 1/2`. -/
theorem shellRatio_le : shellRatio ≤ 6 / 7 := by
  by_contra h
  have h4 : (6 / 7 : ℝ) ^ 4 < shellRatio ^ 4 :=
    pow_lt_pow_left₀ (not_le.1 h) (by norm_num) (by norm_num)
  rw [shellRatio_pow_four] at h4
  norm_num at h4

theorem half_le_shellRatio_sq : (2 : ℝ)⁻¹ ≤ shellRatio ^ 2 := by
  have h1 : shellRatio ^ 2 ≤ 1 := pow_le_one₀ shellRatio_pos.le (shellRatio_le.trans (by norm_num))
  have h0 : 0 ≤ shellRatio ^ 2 := sq_nonneg _
  have h4 := shellRatio_pow_four
  nlinarith

/-- `l_j = ρ 2^{-50} r^j`. -/
theorem shellWidth_eq (ρ : ℝ) (j : ℕ) : shellWidth ρ j = ρ * (2 : ℝ)⁻¹ ^ 50 * shellRatio ^ j := by
  rw [shellWidth, shellRatio, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 4 : ℝ))) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), show -(1 / 4 : ℝ) * (j : ℝ) = -(j : ℝ) / 4 by ring]
  ring

variable {ρ : ℝ}

theorem shellWidth_pos (hρ : 0 < ρ) (j : ℕ) : 0 < shellWidth ρ j := by
  rw [shellWidth_eq]; have := shellRatio_pos; positivity

theorem shellWidth_le (hρ : 0 < ρ) (j : ℕ) : shellWidth ρ j ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by
  rw [shellWidth_eq]
  have h1 : shellRatio ^ j ≤ 1 := pow_le_one₀ shellRatio_pos.le (shellRatio_le.trans (by norm_num))
  have h2 : 0 ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by positivity
  nlinarith

theorem shellWidth_anti (hρ : 0 < ρ) {i k : ℕ} (hik : i ≤ k) : shellWidth ρ k ≤ shellWidth ρ i := by
  rw [shellWidth_eq, shellWidth_eq]
  have h1 : shellRatio ^ k ≤ shellRatio ^ i :=
    pow_le_pow_of_le_one shellRatio_pos.le (shellRatio_le.trans (by norm_num)) hik
  have h2 : 0 ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by positivity
  exact mul_le_mul_of_nonneg_left h1 h2

theorem shellRadius_succ (ρ : ℝ) (j : ℕ) :
    shellRadius ρ (j + 1) = shellRadius ρ j - 32 * shellWidth ρ j := rfl

theorem shellRadius_le (hρ : 0 < ρ) (j : ℕ) : shellRadius ρ j ≤ 3 / 4 * ρ := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => rw [shellRadius_succ]; linarith [shellWidth_pos hρ j]

/-- `d_j ≥ 3ρ/4 - 224 · 2^{-50} ρ (1 - r^j)`: the geometric series `∑ 32 l_i`, with `32 ≤ 224 (1 - r)`. -/
theorem shellRadius_lower (hρ : 0 < ρ) (j : ℕ) :
    3 / 4 * ρ - 224 * (ρ * (2 : ℝ)⁻¹ ^ 50) * (1 - shellRatio ^ j) ≤ shellRadius ρ j := by
  induction j with
  | zero => simp [shellRadius]
  | succ j ih =>
    rw [shellRadius_succ, shellWidth_eq, pow_succ shellRatio j]
    have hu : 0 ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by positivity
    have hq : 0 ≤ shellRatio ^ j := pow_nonneg shellRatio_pos.le j
    have hr := shellRatio_le
    nlinarith [mul_nonneg (mul_nonneg hu hq) (sub_nonneg.2 hr)]

theorem shellRadius_ge (hρ : 0 < ρ) (j : ℕ) :
    3 / 4 * ρ - 224 * (ρ * (2 : ℝ)⁻¹ ^ 50) ≤ shellRadius ρ j := by
  have h := shellRadius_lower hρ j
  have hq : 0 ≤ shellRatio ^ j := pow_nonneg shellRatio_pos.le j
  have hu : 0 ≤ ρ * (2 : ℝ)⁻¹ ^ 50 := by positivity
  nlinarith

/-- Later radii are at least `32 l_i` below `d_i`. -/
theorem shellRadius_le_sub (hρ : 0 < ρ) (i m : ℕ) :
    shellRadius ρ (i + 1 + m) ≤ shellRadius ρ i - 32 * shellWidth ρ i := by
  induction m with
  | zero => exact le_of_eq (shellRadius_succ ρ i)
  | succ m ih =>
    rw [show i + 1 + (m + 1) = i + 1 + m + 1 by ring, shellRadius_succ]
    linarith [shellWidth_pos hρ (i + 1 + m)]

theorem shellRadius_le_sub_of_lt (hρ : 0 < ρ) {i k : ℕ} (hik : i < k) :
    shellRadius ρ k ≤ shellRadius ρ i - 32 * shellWidth ρ i := by
  obtain ⟨m, rfl⟩ : ∃ m, k = i + 1 + m := ⟨k - (i + 1), by omega⟩
  exact shellRadius_le_sub hρ i m

/-- A Minkowski sum with `B_f` moves the distance to `x₀` by less than `f`. -/
theorem abs_dist_sub_lt_of_mem_add {x₀ x : ℂ} {d e f : ℝ} {A : Set ℂ}
    (hA : ∀ y ∈ A, |dist y x₀ - d| ≤ e) (hx : x ∈ A + ball (0 : ℂ) f) : |dist x x₀ - d| < e + f := by
  obtain ⟨y, hy, b, hb, rfl⟩ := hx
  rw [mem_ball_zero_iff] at hb
  have h1 := hA y hy
  have h2 : |dist (y + b) x₀ - dist y x₀| ≤ ‖b‖ := by
    rw [dist_eq_norm, dist_eq_norm]
    have := abs_norm_sub_norm_le (y + b - x₀) (y - x₀)
    rwa [show y + b - x₀ - (y - x₀) = b by ring] at this
  calc |dist (y + b) x₀ - d| ≤ |dist (y + b) x₀ - dist y x₀| + |dist y x₀ - d| := abs_sub_le _ _ _
    _ < e + f := by linarith

theorem abs_dist_sub_lt_of_mem_shell {x₀ x : ℂ} {j : ℕ} (hx : x ∈ shell x₀ ρ j) :
    |dist x x₀ - shellRadius ρ j| < 0 + shellWidth ρ j :=
  abs_dist_sub_lt_of_mem_add (fun y hy => by rw [mem_sphere.1 hy, sub_self, abs_zero]) hx

theorem abs_dist_sub_lt_of_mem_shell_add {x₀ x : ℂ} {j : ℕ}
    (hx : x ∈ shell x₀ ρ j + ball (0 : ℂ) (8 * shellWidth ρ j)) :
    |dist x x₀ - shellRadius ρ j| < 0 + shellWidth ρ j + 8 * shellWidth ρ j :=
  abs_dist_sub_lt_of_mem_add (fun _ hy => (abs_dist_sub_lt_of_mem_shell hy).le) hx

/-- `8 ε_j^{1/2} ρ ≤ 7 l_j` for `N₀ ≥ 200`. -/
theorem eight_sqrt_shellScale_mul_le (hρ : 0 < ρ) {N₀ : ℕ} (hN₀ : 200 ≤ N₀) (j : ℕ) :
    8 * Real.sqrt (shellScale N₀ j) * ρ ≤ 7 * shellWidth ρ j := by
  have hq : 0 ≤ shellRatio ^ j := pow_nonneg shellRatio_pos.le j
  have hε : shellScale N₀ j ≤ ((2 : ℝ)⁻¹ ^ 100 * shellRatio ^ j) ^ 2 := by
    rw [shellScale, dyadicScale]
    calc (2 : ℝ)⁻¹ ^ (N₀ + j) ≤ (2 : ℝ)⁻¹ ^ (200 + j) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (2 : ℝ)⁻¹ ^ 200 * (2 : ℝ)⁻¹ ^ j := pow_add _ _ _
      _ ≤ (2 : ℝ)⁻¹ ^ 200 * (shellRatio ^ 2) ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) half_le_shellRatio_sq j)
            (by norm_num)
      _ = ((2 : ℝ)⁻¹ ^ 100 * shellRatio ^ j) ^ 2 := by ring
  have hs : Real.sqrt (shellScale N₀ j) ≤ (2 : ℝ)⁻¹ ^ 100 * shellRatio ^ j := by
    calc Real.sqrt (shellScale N₀ j) ≤ Real.sqrt (((2 : ℝ)⁻¹ ^ 100 * shellRatio ^ j) ^ 2) :=
          Real.sqrt_le_sqrt hε
      _ = (2 : ℝ)⁻¹ ^ 100 * shellRatio ^ j := Real.sqrt_sq (by positivity)
  rw [shellWidth_eq]
  have ht : 0 ≤ ρ * shellRatio ^ j := by positivity
  have hnum : 8 * (2 : ℝ)⁻¹ ^ 100 ≤ 7 * (2 : ℝ)⁻¹ ^ 50 := by norm_num
  calc 8 * Real.sqrt (shellScale N₀ j) * ρ ≤ 8 * ((2 : ℝ)⁻¹ ^ 100 * shellRatio ^ j) * ρ := by gcongr
    _ = (8 * (2 : ℝ)⁻¹ ^ 100) * (ρ * shellRatio ^ j) := by ring
    _ ≤ (7 * (2 : ℝ)⁻¹ ^ 50) * (ρ * shellRatio ^ j) := mul_le_mul_of_nonneg_right hnum ht
    _ = 7 * (ρ * (2 : ℝ)⁻¹ ^ 50 * shellRatio ^ j) := by ring

end Section6

open Section6

/-- **Lemma 6.12** (lemma:shell-decomposition, line 1636). -/
theorem shellDecompositionStmt_proved : ShellDecompositionStmt := by
  intro ρ hρ x₀ _ N₀ hN₀
  have hρ0 : 0 < ρ := hρ.1
  have hL : ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ / 2 ^ 40 := by
    have : (2 : ℝ)⁻¹ ^ 50 ≤ 1 / 2 ^ 40 := by norm_num
    calc ρ * (2 : ℝ)⁻¹ ^ 50 ≤ ρ * (1 / 2 ^ 40) := mul_le_mul_of_nonneg_left this hρ0.le
      _ = ρ / 2 ^ 40 := by ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- the union lies in the closed annulus `3ρ/5 ≤ |x - x₀| ≤ 9ρ/10`
    have hsub : (⋃ j, shell x₀ ρ j + ball (0 : ℂ) (8 * shellWidth ρ j)) ⊆
        closedBall x₀ (9 / 10 * ρ) \ ball x₀ (3 / 5 * ρ) := by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      have h1 := abs_lt.1 (abs_dist_sub_lt_of_mem_shell_add hj)
      have h2 := shellRadius_ge hρ0 j
      have h3 := shellRadius_le hρ0 j
      have h4 := shellWidth_le hρ0 j
      refine ⟨mem_closedBall.2 (by linarith), fun hb => ?_⟩
      have := mem_ball.1 hb
      linarith
    have hcl := closure_minimal hsub (isClosed_closedBall.sdiff isOpen_ball)
    exact (isCompact_closedBall x₀ (9 / 10 * ρ)).of_isClosed_subset isClosed_closure
      (hcl.trans sdiff_subset)
  · have hsub : (⋃ j, shell x₀ ρ j + ball (0 : ℂ) (8 * shellWidth ρ j)) ⊆
        closedBall x₀ (9 / 10 * ρ) \ ball x₀ (3 / 5 * ρ) := by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      have h1 := abs_lt.1 (abs_dist_sub_lt_of_mem_shell_add hj)
      have h2 := shellRadius_ge hρ0 j
      have h3 := shellRadius_le hρ0 j
      have h4 := shellWidth_le hρ0 j
      refine ⟨mem_closedBall.2 (by linarith), fun hb => ?_⟩
      have := mem_ball.1 hb
      linarith
    refine (closure_minimal hsub (isClosed_closedBall.sdiff isOpen_ball)).trans fun x hx => ?_
    have h1 := mem_closedBall.1 hx.1
    have h2 : ¬ dist x x₀ < 3 / 5 * ρ := fun h => hx.2 (mem_ball.2 h)
    refine ⟨mem_ball.2 (by linarith), fun hc => ?_⟩
    have := mem_closedBall.1 hc
    linarith
  · -- the shells are separated
    intro j
    refine eq_empty_iff_forall_notMem.2 fun x ⟨hx1, hx2⟩ => ?_
    simp only [mem_iUnion] at hx2
    obtain ⟨j', hj', hx'⟩ := hx2
    have h1 := abs_lt.1 (abs_dist_sub_lt_of_mem_shell_add hx1)
    have h2 := abs_lt.1 (abs_dist_sub_lt_of_mem_shell hx')
    have hl := shellWidth_pos hρ0 j
    rcases lt_or_gt_of_ne (hj' : j' ≠ j) with h | h
    · have h3 := shellRadius_le_sub_of_lt hρ0 h
      have h4 := shellWidth_anti hρ0 h.le
      linarith
    · have h3 := shellRadius_le_sub_of_lt hρ0 h
      have h4 := shellWidth_anti hρ0 h.le
      linarith
  · intro j w hw
    have h1 := abs_lt.1 (abs_dist_sub_lt_of_mem_shell hw)
    have h2 := shellRadius_ge hρ0 j
    have h3 := shellRadius_le hρ0 j
    have h4 := shellWidth_le hρ0 j
    have h5 := eight_sqrt_shellScale_mul_le hρ0 hN₀ j
    have h6 := shellWidth_pos hρ0 j
    refine ⟨fun y hy => ?_, sdiff_subset_sdiff_left (ball_subset_ball ?_)⟩
    · have hyw := mem_ball.1 hy
      have t1 := dist_triangle y w x₀
      have t2 := dist_triangle w y x₀
      rw [dist_comm w y] at t2
      refine ⟨mem_ball.2 ?_, fun hc => ?_⟩
      · rw [shellOuterRadius]; linarith
      · have := mem_closedBall.1 hc
        linarith
    · rw [shellOuterRadius]; linarith

end HarmonicBalls

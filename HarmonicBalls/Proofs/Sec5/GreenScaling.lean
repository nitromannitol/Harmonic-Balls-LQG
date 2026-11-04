import HarmonicBalls.Proofs.Potential.GreenBall

/-! # Scaling the Green function of a disc -/

namespace HarmonicBalls

open MeasureTheory Metric

/-- The explicit Green function of a disc is invariant under positive
simultaneous dilation of its radius and arguments. -/
theorem greenBall_smul {R k : ℝ} (hk : 0 < k) (x y : ℂ) :
    greenBall (k * R) (k • x) (k • y) = greenBall R x y := by
  have hnum : ((k * R : ℝ) : ℂ) ^ 2 - starRingEnd ℂ (k • x) * (k • y) =
      (k : ℂ) ^ 2 * ((R : ℂ) ^ 2 - starRingEnd ℂ x * y) := by
    simp only [Complex.real_smul, Complex.ofReal_mul, map_mul, Complex.conj_ofReal]
    ring
  have hdiff : k • x - k • y = (k : ℂ) * (x - y) := by
    simp only [Complex.real_smul]
    ring
  unfold greenBall
  rw [hnum, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, hdiff,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  have hden : k * R * (k * ‖x - y‖) = k ^ 2 * (R * ‖x - y‖) := by ring
  rw [hden, mul_div_mul_left _ _ (pow_ne_zero 2 hk.ne')]

/-- The Green function of a disc is invariant under positive simultaneous
dilation, including at the diagonal and outside the disc. -/
theorem greenFunction_ball_smul {R k : ℝ} (hk : 0 < k) (x y : ℂ) :
    greenFunction (ball 0 (k * R)) (k • x) (k • y) = greenFunction (ball 0 R) x y := by
  have hmem (z : ℂ) : k • z ∈ ball (0 : ℂ) (k * R) ↔ z ∈ ball (0 : ℂ) R := by
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    exact mul_lt_mul_iff_right₀ hk
  by_cases hx : x ∈ ball (0 : ℂ) R
  · by_cases hy : y ∈ ball (0 : ℂ) R
    · by_cases hxy : x = y
      · subst y
        simp only [greenFunction_self]
      · have hxy' : k • x ≠ k • y := by
          intro heq
          apply hxy
          have h := congrArg (fun z : ℂ => k⁻¹ • z) heq
          simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h
        rw [greenFunction_ball ((hmem x).2 hx) ((hmem y).2 hy) hxy',
          greenFunction_ball hx hy hxy, greenBall_smul hk]
    · rw [greenFunction_of_notMem_right (by simpa only [hmem] using hy),
        greenFunction_of_notMem_right hy]
  · rw [greenFunction_of_notMem_left (by simpa only [hmem] using hx),
      greenFunction_of_notMem_left hx]

end HarmonicBalls

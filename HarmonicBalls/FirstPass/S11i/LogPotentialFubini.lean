import HarmonicBalls.FirstPass.S11i.LogPotential

/-!
# Step 8 helper: Fubini for the logarithmic potential of test functions

Source: corrected paper, lemma `s11-pinch:lem:mixing` (tex lines 3769-3812). The covariance of the dilated
test function is `∫ f x * ∫ z, k z * log ‖x - 2⁻ⁿ z‖` (`integral_dilateTest_wholePlaneCov`); exchanging the two
integrals (Fubini, justified by a translation-invariant dominating function) turns it into
`∫ z, k z * G_f(2⁻ⁿ z)` with the logarithmic potential `G_f` of `f` (`continuous_logPotential`).

Deterministic lemmas only: no probability, no Gaussian input.
-/

open MeasureTheory Filter Topology Metric Set
open scoped Convolution

namespace HarmonicBalls

/-- `|log ‖u‖|` on the ball of radius `T` about `0`, extended by zero outside the ball. -/
noncomputable def logAbsBall (T : ℝ) (u : ℂ) : ℝ :=
  (ball (0 : ℂ) T).indicator (fun u => |Real.log ‖u‖|) u

theorem logAbsBall_nonneg (T : ℝ) (u : ℂ) : 0 ≤ logAbsBall T u :=
  indicator_nonneg (fun _ _ => abs_nonneg _) u

theorem measurable_logAbsBall (T : ℝ) : Measurable (logAbsBall T) := by
  unfold logAbsBall
  have h : Measurable fun u : ℂ => |Real.log ‖u‖| := by fun_prop
  exact h.indicator measurableSet_ball

theorem integrable_logAbsBall (T : ℝ) : Integrable (logAbsBall T) := by
  unfold logAbsBall
  rw [integrable_indicator_iff measurableSet_ball]
  exact (integrableOn_log_norm_ball T).abs

/-- A translation-invariant dominating function on `ℂ × ℂ`: `Cfk` times the indicator of `z ∈ closedBall 0 R`
times `logAbsBall` evaluated at `x - c • z`. -/
theorem integrable_dominator_logPotential (R Cfk c : ℝ) :
    Integrable (fun p : ℂ × ℂ =>
      (closedBall (0 : ℂ) R).indicator (fun _ => Cfk) p.2 * logAbsBall (2 * R + 1) (p.1 - c • p.2))
      (volume.prod volume) := by
  have hmeas : Measurable (fun p : ℂ × ℂ =>
      (closedBall (0 : ℂ) R).indicator (fun _ => Cfk) p.2 * logAbsBall (2 * R + 1) (p.1 - c • p.2)) := by
    apply Measurable.mul
    · exact (measurable_const.indicator measurableSet_closedBall).comp measurable_snd
    · exact (measurable_logAbsBall _).comp (measurable_fst.sub (measurable_snd.const_smul c))
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun z => ?_, ?_⟩
  · show Integrable (fun x : ℂ => (closedBall (0 : ℂ) R).indicator (fun _ => Cfk) z *
        logAbsBall (2 * R + 1) (x - c • z)) volume
    exact ((integrable_logAbsBall _).comp_sub_right (c • z)).const_mul _
  · have key : Integrable (fun z : ℂ =>
        ‖(closedBall (0 : ℂ) R).indicator (fun _ => Cfk) z‖ * ∫ u, logAbsBall (2 * R + 1) u) volume := by
      have hind : (fun z : ℂ =>
          ‖(closedBall (0 : ℂ) R).indicator (fun _ => Cfk) z‖ * ∫ u, logAbsBall (2 * R + 1) u)
          = (closedBall (0 : ℂ) R).indicator (fun _ => ‖Cfk‖ * ∫ u, logAbsBall (2 * R + 1) u) := by
        funext z
        by_cases hz : z ∈ closedBall (0 : ℂ) R <;> simp [hz]
      rw [hind, integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const (measure_closedBall_lt_top).ne
    refine key.congr (ae_of_all _ fun z => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg, logAbsBall_nonneg]
    rw [integral_const_mul, integral_sub_right_eq_self]

/-- The product `(x, z) ↦ f x * (k z * log ‖x - c • z‖)` is integrable on `ℂ × ℂ` for test functions `f, k`
supported in `closedBall 0 R` and a real `c ∈ [0, 1]`. -/
theorem integrable_uncurry_mul_logPotential {f k : ℂ → ℝ} (hf : IsTestFunction univ f)
    (hk : IsTestFunction univ k) {R c : ℝ} (hfR : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) (hkR : ∀ z, k z ≠ 0 → ‖z‖ ≤ R)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Integrable (Function.uncurry fun x z => f x * (k z * Real.log ‖x - c • z‖)) (volume.prod volume) := by
  obtain ⟨Cf, hCf⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
  obtain ⟨Ck, hCk⟩ := hk.1.continuous.bounded_above_of_compact_support hk.2.1
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  have hCk0 : 0 ≤ Ck := (norm_nonneg _).trans (hCk 0)
  refine Integrable.mono' (integrable_dominator_logPotential R (Cf * Ck) c) ?_ ?_
  · have h1 : Measurable fun p : ℂ × ℂ => f p.1 * (k p.2 * Real.log ‖p.1 - c • p.2‖) := by
      have hfm : Measurable f := hf.1.continuous.measurable
      have hkm : Measurable k := hk.1.continuous.measurable
      exact (hfm.comp measurable_fst).mul ((hkm.comp measurable_snd).mul
        (Real.measurable_log.comp (measurable_norm.comp (measurable_fst.sub (measurable_snd.const_smul c)))))
    exact h1.aestronglyMeasurable
  · refine ae_of_all _ fun p => ?_
    obtain ⟨x, z⟩ := p
    simp only [Function.uncurry_apply_pair]
    by_cases hx : f x = 0
    · simp only [hx, zero_mul, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => mul_nonneg hCf0 hCk0) _) (logAbsBall_nonneg _ _)
    by_cases hz : k z = 0
    · simp only [hz, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => mul_nonneg hCf0 hCk0) _) (logAbsBall_nonneg _ _)
    have hxR := hfR x hx
    have hzR := hkR z hz
    have hcz : ‖c • z‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      have := mul_le_mul_of_nonneg_right hc1 (norm_nonneg z)
      linarith
    have hxz : x - c • z ∈ ball (0 : ℂ) (2 * R + 1) := by
      rw [mem_ball_zero_iff]
      have := norm_sub_le x (c • z)
      linarith
    have hH : logAbsBall (2 * R + 1) (x - c • z) = |Real.log ‖x - c • z‖| := by
      unfold logAbsBall
      rw [indicator_of_mem hxz]
    have hz' : z ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 hzR
    rw [indicator_of_mem hz', hH, norm_mul, norm_mul, Real.norm_eq_abs (Real.log ‖x - c • z‖)]
    have h2 := mul_le_mul (hCf x) (mul_le_mul_of_nonneg_right (hCk z) (abs_nonneg (Real.log ‖x - c • z‖)))
      (mul_nonneg (norm_nonneg _) (abs_nonneg _)) hCf0
    exact h2.trans (le_of_eq (by ring))

/-- Fubini for the logarithmic potential: for test functions `f, k` and `c ∈ [0, 1]`,
`∫ x, f x * ∫ z, k z * log ‖x - c • z‖ = ∫ z, k z * ∫ x, f x * log ‖x - c • z‖`. -/
theorem integral_mul_logPotential_swap {f k : ℂ → ℝ} (hf : IsTestFunction univ f)
    (hk : IsTestFunction univ k) {R c : ℝ} (hfR : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) (hkR : ∀ z, k z ≠ 0 → ‖z‖ ≤ R)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∫ x, f x * ∫ z, k z * Real.log ‖x - c • z‖ = ∫ z, k z * ∫ x, f x * Real.log ‖x - c • z‖ := by
  have hint := integrable_uncurry_mul_logPotential hf hk hfR hkR hc0 hc1
  calc ∫ x, f x * ∫ z, k z * Real.log ‖x - c • z‖
      = ∫ x, ∫ z, f x * (k z * Real.log ‖x - c • z‖) := by
        congr 1
        funext x
        exact (integral_const_mul _ _).symm
    _ = ∫ z, ∫ x, f x * (k z * Real.log ‖x - c • z‖) := integral_integral_swap hint
    _ = ∫ z, k z * ∫ x, f x * Real.log ‖x - c • z‖ := by
        congr 1
        funext z
        rw [← integral_const_mul]
        congr 1
        funext x
        ring

end HarmonicBalls

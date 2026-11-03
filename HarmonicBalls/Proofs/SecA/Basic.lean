import HarmonicBalls.Steps.SecA.Basic
import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Potential.GreenPositivity
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Appendix A, shared steps: superharmonic functions and the distributional Laplacian

Proofs of the Basic leaves of `HarmonicBalls/Steps/SecA/Basic.lean` (Appendix A, sec:obstacle-appendix, of the
corrected draft of Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity*, arXiv:2208.11795).

## Main results

* `superharmonicOfLaplacianLEStep_holds` (Weyl's lemma, superharmonic form, I4): a continuous `w` with `Δw ≤ 0` in
  the distributional sense on an open `U` is classically superharmonic on `U`.
* `laplacianLEOfSuperharmonicStep_holds`: conversely, a continuous classically superharmonic `w` has `Δw ≤ 0`.
* `hasLaplacianOfLaplacianLEGEStep_holds`: `Δw ≤ 0` and `Δw ≥ 0` on an open `U` give `Δw = 0` on `U`.
* `obstacleTendstoAtBotStep_holds`: the obstacle `β_t = -t G_{B_R}(z, ·) + q_{B_R}` tends to `-∞` at the pole.

## Green's identity for circle averages

The common tool is the identity, for a compactly supported `C²` function `φ` on the plane and `r > 0`,
`∫ log⁺ (r / |y - x|) Δφ(y) dy = 2π (M(φ; x, r) - φ(x))` (`integral_posLog_mul_laplacian`), where `M(φ; x, r)` is
the average of `φ` over the circle `∂B_r(x)`. The kernel `(2π)⁻¹ log⁺ (r / |y - x|)` is the Green function of the
disc `B_r(x)` with pole `x`. The identity follows from the fundamental solution identity
`∫ log |y - x| Δφ(y) dy = 2π φ(x)` (`integral_log_norm_sub_mul_laplacian`), the circle average
`M(log |y - ·|; x, r) = log r + log⁺ (|x - y| / r)` (Mathlib, `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`)
and Fubini.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian Real
open scoped ContDiff

/-! ## Green's identity for circle averages -/

/-- Fubini integrability: `(θ, y) ↦ log |y - x - r e^{iθ}| Δφ(y)` is integrable on `[0, 2π] × ℂ` for a compactly
supported `C²` function `φ`. Proof: the shear `(θ, y) ↦ (θ, y - x - r e^{iθ})` preserves the product measure and turns
the integrand into `log |v| Δφ(v + x + r e^{iθ})`, which is dominated by `C |log |v|| 1_{|v| ≤ B}`. -/
theorem integrable_log_norm_sub_circleMap_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (x : ℂ) (r : ℝ) :
    Integrable (Function.uncurry fun θ y => Real.log ‖y - circleMap x r θ‖ * Δ φ y)
      ((volume.restrict (Set.uIoc 0 (2 * π))).prod volume) := by
  set μI : Measure ℝ := volume.restrict (Set.uIoc 0 (2 * π))
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff hφ
  have hΔs : HasCompactSupport (Δ φ) := hasCompactSupport_laplacian hc
  obtain ⟨C, hC⟩ := hΔc.bounded_above_of_compact_support hΔs
  obtain ⟨A, hA⟩ := hΔs.isCompact.isBounded.subset_closedBall 0
  set B : ℝ := A + ‖x‖ + |r|
  have hcm : Continuous (circleMap x r) := continuous_circleMap x r
  have hshear : MeasurePreserving (fun p : ℝ × ℂ => (p.1, p.2 - circleMap x r p.1)) (μI.prod volume)
      (μI.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id μI)
      (by fun_prop) (Eventually.of_forall fun θ => map_sub_right_eq_self volume _)
  set G : ℝ × ℂ → ℝ := fun p => Real.log ‖p.2‖ * Δ φ (p.2 + circleMap x r p.1)
  have hg : Integrable ((closedBall (0 : ℂ) B).indicator fun v => C * |Real.log ‖v‖|) volume := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_closedBall
    have h1 : IntegrableOn (fun v : ℂ => Real.log ‖v‖) (closedBall 0 B) :=
      (integrableOn_ball_log_norm (B + 1)).mono_set (closedBall_subset_ball (by linarith))
    exact h1.abs.const_mul C
  have h1I : Integrable (fun _ : ℝ => (1 : ℝ)) μI :=
    (intervalIntegrable_const (μ := volume) (a := 0) (b := 2 * π) (c := (1 : ℝ))).def'
  have hGm : AEStronglyMeasurable G (μI.prod volume) := by
    refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact Real.measurable_log.comp (measurable_norm.comp measurable_snd)
    · exact (hΔc.comp (continuous_snd.add (hcm.comp continuous_fst))).measurable
  have hG : Integrable G (μI.prod volume) := by
    refine Integrable.mono' (h1I.mul_prod hg) hGm (Eventually.of_forall fun p => ?_)
    simp only [G, one_mul, norm_mul, Real.norm_eq_abs]
    by_cases hp : p.2 + circleMap x r p.1 ∈ tsupport (Δ φ)
    · have hB : p.2 ∈ closedBall (0 : ℂ) B := by
        have h1 := hA hp
        rw [mem_closedBall, dist_zero_right] at h1 ⊢
        have h2 : ‖circleMap x r p.1‖ ≤ ‖x‖ + |r| := by
          rw [circleMap]
          refine (norm_add_le _ _).trans ?_
          simp [Complex.norm_exp_ofReal_mul_I]
        calc ‖p.2‖ = ‖(p.2 + circleMap x r p.1) - circleMap x r p.1‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖p.2 + circleMap x r p.1‖ + ‖circleMap x r p.1‖ := norm_sub_le _ _
          _ ≤ B := by simp only [B]; linarith
      rw [indicator_of_mem hB, mul_comm C]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC _) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hp, abs_zero, mul_zero]
      exact indicator_nonneg (fun v _ => mul_nonneg ((norm_nonneg _).trans (hC 0)) (abs_nonneg _)) _
  convert hshear.integrable_comp_of_integrable hG using 1
  ext ⟨θ, y⟩
  simp [G]

/-- Integrability of `y ↦ log |y - x| Δφ(y)` for a compactly supported `C²` function `φ`. -/
theorem integrable_log_norm_sub_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (x : ℂ) : Integrable (fun y => Real.log ‖y - x‖ * Δ φ y) := by
  have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
    ).integrable_smul_right_of_hasCompactSupport (continuous_laplacian_of_contDiff hφ)
    (hasCompactSupport_laplacian hc)
  simpa [smul_eq_mul] using h

/-- **Green's identity for circle averages.** For a compactly supported `C²` function `φ` on the plane and `r > 0`,
`∫ log⁺ (r / |y - x|) Δφ(y) dy = 2π (M(φ; x, r) - φ(x))`, where `M(φ; x, r)` is the circle average. Equivalently,
`(2π)⁻¹ log⁺ (r / |y - x|)`, the Green function of `B_r(x)` with pole `x`, represents `M(φ; x, r) - φ(x)`. -/
theorem integral_posLog_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (x : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∫ y, log⁺ (r / ‖y - x‖) * Δ φ y = 2 * π * (circleAverage φ x r - φ x) := by
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff hφ
  have hΔs : HasCompactSupport (Δ φ) := hasCompactSupport_laplacian hc
  have hint_log := integrable_log_norm_sub_mul_laplacian hφ hc x
  have hint_pos : Integrable (fun y => (Real.log r + log⁺ (r⁻¹ * ‖x - y‖)) * Δ φ y) :=
    (Continuous.mul (by fun_prop) hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  have hswap : ∫ y, (Real.log r + log⁺ (r⁻¹ * ‖x - y‖)) * Δ φ y = 2 * π * circleAverage φ x r := by
    have h1 : ∀ y, Real.log r + log⁺ (r⁻¹ * ‖x - y‖) =
        (2 * π)⁻¹ * ∫ θ in 0..2 * π, Real.log ‖y - circleMap x r θ‖ := by
      intro y
      rw [← circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne', circleAverage_def,
        smul_eq_mul]
      simp_rw [norm_sub_rev (circleMap x r _) y]
    simp_rw [h1]
    calc ∫ y, (2 * π)⁻¹ * (∫ θ in 0..2 * π, Real.log ‖y - circleMap x r θ‖) * Δ φ y
        = (2 * π)⁻¹ * ∫ y, ∫ θ in 0..2 * π, Real.log ‖y - circleMap x r θ‖ * Δ φ y := by
          rw [← integral_const_mul]
          congr 1
          ext y
          rw [intervalIntegral.integral_mul_const]
          ring
      _ = (2 * π)⁻¹ * ∫ θ in 0..2 * π, ∫ y, Real.log ‖y - circleMap x r θ‖ * Δ φ y := by
          rw [intervalIntegral_integral_swap (integrable_log_norm_sub_circleMap_mul_laplacian hφ hc x r)]
      _ = (2 * π)⁻¹ * ∫ θ in 0..2 * π, 2 * π * φ (circleMap x r θ) := by
          simp_rw [integral_log_norm_sub_mul_laplacian hφ hc]
      _ = 2 * π * circleAverage φ x r := by
          rw [intervalIntegral.integral_const_mul, circleAverage_def, smul_eq_mul]
          ring
  have hpt : ∀ᵐ y : ℂ, log⁺ (r / ‖y - x‖) * Δ φ y =
      (Real.log r + log⁺ (r⁻¹ * ‖x - y‖)) * Δ φ y - Real.log ‖y - x‖ * Δ φ y := by
    filter_upwards [ae_ne_complex x] with y hy
    have hn : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hy)
    have h := posLog_sub_posLog_inv (x := r⁻¹ * ‖x - y‖)
    rw [norm_sub_rev x y] at h
    have hinv : (r⁻¹ * ‖y - x‖)⁻¹ = r / ‖y - x‖ := by rw [mul_inv, inv_inv, div_eq_mul_inv]
    rw [hinv, Real.log_mul (inv_ne_zero hr.ne') hn, Real.log_inv] at h
    rw [norm_sub_rev x y]
    linear_combination (-(Δ φ y)) * h
  rw [integral_congr_ae hpt, integral_sub hint_pos hint_log, hswap,
    integral_log_norm_sub_mul_laplacian hφ hc]
  ring

/-! ## Exchanging a circle average with an integral over the plane -/

/-- The circle `∂B_r(y)` traversed with radius `-r`: `circleMap y (-r) θ = y - circleMap 0 r θ`. -/
theorem circleMap_neg_radius_eq_sub (y : ℂ) (r θ : ℝ) : circleMap y (-r) θ = y - circleMap 0 r θ := by
  simp [circleMap, sub_eq_add_neg]

/-- `circleMap y r θ = y + circleMap 0 r θ`. -/
theorem circleMap_eq_add_circleMap_zero (y : ℂ) (r θ : ℝ) : circleMap y r θ = y + circleMap 0 r θ := by
  simp [circleMap]

/-- **Exchanging a circle average with an integral over the plane.** For `f` bounded and a.e. strongly measurable and
`g` continuous with compact support, `∫ f(y) M(g; y, r) dy = ∫ g(y) M(f; y, r) dy`, both integrands being
integrable. This is the symmetry of the circle-average operator on `L²` of the plane. -/
theorem integral_mul_circleAverage_comm {f g : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {Bf : ℝ}
    (hBf : ∀ y, |f y| ≤ Bf) (hg : Continuous g) (hgs : HasCompactSupport g) (r : ℝ) :
    Integrable (fun y => f y * circleAverage g y r) ∧ Integrable (fun y => g y * circleAverage f y r) ∧
      ∫ y, f y * circleAverage g y r = ∫ y, g y * circleAverage f y r := by
  set μI : Measure ℝ := volume.restrict (Set.uIoc 0 (2 * π))
  set e : ℝ → ℂ := circleMap 0 r
  have he : Continuous e := continuous_circleMap 0 r
  have hplus : MeasurePreserving (fun p : ℝ × ℂ => (p.1, p.2 + e p.1)) (μI.prod volume) (μI.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id μI)
      (by fun_prop) (Eventually.of_forall fun θ => map_add_right_eq_self volume _)
  have hminus : MeasurePreserving (fun p : ℝ × ℂ => (p.1, p.2 - e p.1)) (μI.prod volume) (μI.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id μI)
      (by fun_prop) (Eventually.of_forall fun θ => map_sub_right_eq_self volume _)
  set Ψ : ℝ × ℂ → ℝ := fun p => f (p.2 - e p.1) * g p.2
  set Φ : ℝ × ℂ → ℝ := fun p => f p.2 * g (p.2 + e p.1)
  have hΦΨ : Ψ ∘ (fun p : ℝ × ℂ => (p.1, p.2 + e p.1)) = Φ := by
    ext p; simp [Ψ, Φ]
  have h1I : Integrable (fun _ : ℝ => (1 : ℝ)) μI :=
    (intervalIntegrable_const (μ := volume) (a := 0) (b := 2 * π) (c := (1 : ℝ))).def'
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgs
  have hΨm : AEStronglyMeasurable Ψ (μI.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℂ => f p.2) (μI.prod volume) := hf.comp_snd
    have h2 := h1.comp_measurePreserving hminus
    exact h2.mul (hg.comp continuous_snd).aestronglyMeasurable
  have hΨ : Integrable Ψ (μI.prod volume) := by
    refine Integrable.mono' (h1I.mul_prod (hgi.norm.const_mul Bf)) hΨm (Eventually.of_forall fun p => ?_)
    simp only [Ψ, one_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hBf _) (abs_nonneg _)
  have hΦ : Integrable Φ (μI.prod volume) := hΦΨ ▸ hplus.integrable_comp_of_integrable hΨ
  have hint : ∫ p, Φ p ∂(μI.prod volume) = ∫ p, Ψ p ∂(μI.prod volume) := by
    rw [← hΦΨ]
    have h := integral_map (μ := μI.prod volume) hplus.aemeasurable (f := Ψ) (by rw [hplus.map_eq]; exact hΨm)
    rw [hplus.map_eq] at h
    exact h.symm
  have h02 : (0 : ℝ) ≤ 2 * π := by positivity
  have hL : ∀ y, f y * circleAverage g y r = (2 * π)⁻¹ * ∫ θ, Φ (θ, y) ∂μI := by
    intro y
    simp only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h02, μI,
      Set.uIoc_of_le h02, Φ, e, circleMap_eq_add_circleMap_zero y r, integral_const_mul]
    ring
  have hR : ∀ y, g y * circleAverage f y r = (2 * π)⁻¹ * ∫ θ, Ψ (θ, y) ∂μI := by
    intro y
    rw [← circleAverage_neg_radius]
    simp only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h02, μI,
      Set.uIoc_of_le h02, Ψ, e, circleMap_neg_radius_eq_sub y r, integral_mul_const]
    ring
  simp_rw [hL, hR]
  refine ⟨hΦ.integral_prod_right.const_mul _, hΨ.integral_prod_right.const_mul _, ?_⟩
  rw [integral_const_mul, integral_const_mul, ← integral_prod_symm _ hΦ, ← integral_prod_symm _ hΨ, hint]

/-! ## The Green kernel `log⁺ (r / |v|)` of a disc -/

/-- `log⁺ (r / |v|) = 0` for `|v| ≥ r ≥ 0`. -/
theorem posLog_div_norm_eq_zero {r : ℝ} (hr : 0 ≤ r) {v : ℂ} (hv : r ≤ ‖v‖) : log⁺ (r / ‖v‖) = 0 := by
  rw [posLog_eq_zero_iff, abs_of_nonneg (div_nonneg hr (norm_nonneg _))]
  rcases eq_or_lt_of_le (norm_nonneg v) with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · exact (div_le_one h).2 hv

/-- The kernel `v ↦ log⁺ (r / |v|)` is integrable on the plane. -/
theorem integrable_posLog_div_norm {r : ℝ} (hr : 0 < r) : Integrable (fun v : ℂ => log⁺ (r / ‖v‖)) := by
  have hm : Measurable fun v : ℂ => log⁺ (r / ‖v‖) :=
    continuous_posLog.measurable.comp (measurable_const.div measurable_norm)
  have hg : Integrable ((closedBall (0 : ℂ) r).indicator fun v => |Real.log r| + |Real.log ‖v‖|) := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_closedBall
    have h1 : IntegrableOn (fun v : ℂ => Real.log ‖v‖) (closedBall 0 r) :=
      (integrableOn_ball_log_norm (r + 1)).mono_set (closedBall_subset_ball (by linarith))
    exact (integrableOn_const measure_closedBall_lt_top.ne).add h1.abs
  refine Integrable.mono' hg hm.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg posLog_nonneg]
  by_cases hv : r ≤ ‖v‖
  · rw [posLog_div_norm_eq_zero hr.le hv]
    exact indicator_nonneg (fun _ _ => by positivity) _
  · push Not at hv
    rw [indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact hv.le)]
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h, div_zero, posLog_zero]; positivity
    · rw [posLog_apply, Real.log_div hr.ne' h.ne']
      refine max_le (by positivity) ?_
      linarith [le_abs_self (Real.log r), neg_abs_le (Real.log ‖v‖)]

/-- The kernel `v ↦ log⁺ (r / |v|)` has positive integral for `r > 0`. -/
theorem integral_posLog_div_norm_pos {r : ℝ} (hr : 0 < r) : 0 < ∫ v : ℂ, log⁺ (r / ‖v‖) := by
  rw [integral_pos_iff_support_of_nonneg (fun v => posLog_nonneg) (integrable_posLog_div_norm hr)]
  have hsub : {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < r} ⊆ Function.support fun v : ℂ => log⁺ (r / ‖v‖) := by
    rintro v ⟨h0, hr'⟩
    rw [Function.mem_support, Ne, posLog_eq_zero_iff, not_le, abs_of_pos (div_pos hr h0)]
    exact (one_lt_div h0).2 hr'
  have hopen : IsOpen {v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < r} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hne : ({v : ℂ | 0 < ‖v‖ ∧ ‖v‖ < r}).Nonempty :=
    ⟨((r / 2 : ℝ) : ℂ), by simp only [mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]; constructor <;> linarith⟩
  exact (hopen.measure_pos volume hne).trans_le (measure_mono hsub)

/-- Green's identity for circle averages, in translated form:
`∫ log⁺ (r / |v|) Δφ(x + v) dv = 2π (M(φ; x, r) - φ(x))`. -/
theorem integral_posLog_mul_laplacian_add {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ v, log⁺ (r / ‖v‖) * Δ φ (v + x) = 2 * π * (circleAverage φ x r - φ x) := by
  rw [← integral_posLog_mul_laplacian hφ hc x hr]
  have h := integral_add_right_eq_self (μ := volume) (fun y => log⁺ (r / ‖y - x‖) * Δ φ y) x
  simpa only [add_sub_cancel_right] using h

/-- **Second-order expansion of circle averages, uniformly.** If `|Δφ(y + v) - Δφ(y)| ≤ ε` whenever `|v| < r`, then
`|2π (M(φ; y, r) - φ(y)) - κ_r Δφ(y)| ≤ ε κ_r`, where `κ_r = ∫ log⁺ (r / |v|) dv` (`= π r² / 2`). -/
theorem abs_circleAverage_sub_sub_le {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {r ε : ℝ} (hr : 0 < r) (y : ℂ) (hε : ∀ v : ℂ, ‖v‖ < r → |Δ φ (v + y) - Δ φ y| ≤ ε) :
    |2 * π * (circleAverage φ y r - φ y) - (∫ v : ℂ, log⁺ (r / ‖v‖)) * Δ φ y| ≤
      ε * ∫ v : ℂ, log⁺ (r / ‖v‖) := by
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff hφ
  obtain ⟨C, hC⟩ := hΔc.bounded_above_of_compact_support (hasCompactSupport_laplacian hc)
  have hk := integrable_posLog_div_norm hr
  have hi1 : Integrable (fun v : ℂ => Δ φ (v + y) * log⁺ (r / ‖v‖)) :=
    hk.bdd_mul (hΔc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun v => hC _)
  have hi1' : Integrable (fun v : ℂ => log⁺ (r / ‖v‖) * Δ φ (v + y)) := by
    simpa only [mul_comm] using hi1
  rw [← integral_posLog_mul_laplacian_add hφ hc y hr, ← integral_mul_const, ← integral_sub hi1'
    (hk.mul_const _), ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun v => abs_nonneg _) (hk.const_mul ε) (Eventually.of_forall fun v => ?_))
  dsimp only
  rw [← mul_sub, abs_mul, abs_of_nonneg posLog_nonneg, mul_comm ε]
  by_cases hv : ‖v‖ < r
  · exact mul_le_mul_of_nonneg_left (hε v hv) posLog_nonneg
  · rw [posLog_div_norm_eq_zero hr.le (not_lt.1 hv), zero_mul, zero_mul]

/-- The Laplacian commutes with translations: `Δ(ρ(· - a)) = (Δρ)(· - a)`. -/
theorem laplacian_comp_sub_const (ρ : ℂ → ℝ) (a t : ℂ) : Δ (fun z => ρ (z - a)) t = Δ ρ (t - a) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_comp_sub]

/-- **Circle averages of a correlation.** For `f` bounded and a.e. strongly measurable and `g` continuous with
compact support, the correlation `u(z) = ∫ f(t) g(t - z) dt` is circle integrable and
`M(u; x, r) = ∫ f(t) M(g; t - x, r) dt` (Fubini). -/
theorem circleAverage_integral_mul_sub {f g : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hB : ∀ t, |f t| ≤ B) (hg : Continuous g) (hgs : HasCompactSupport g) (x : ℂ) (r : ℝ) :
    CircleIntegrable (fun z => ∫ t, f t * g (t - z)) x r ∧
      Integrable (fun t => f t * circleAverage g (t - x) r) ∧
      circleAverage (fun z => ∫ t, f t * g (t - z)) x r = ∫ t, f t * circleAverage g (t - x) r := by
  set μI : Measure ℝ := volume.restrict (Set.uIoc 0 (2 * π))
  have hcm : Continuous (circleMap x r) := continuous_circleMap x r
  have hminus : MeasurePreserving (fun p : ℝ × ℂ => (p.1, p.2 - circleMap x r p.1)) (μI.prod volume)
      (μI.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id μI)
      (by fun_prop) (Eventually.of_forall fun θ => map_sub_right_eq_self volume _)
  have h1I : Integrable (fun _ : ℝ => (1 : ℝ)) μI :=
    (intervalIntegrable_const (μ := volume) (a := 0) (b := 2 * π) (c := (1 : ℝ))).def'
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgs
  set Φ : ℝ × ℂ → ℝ := fun p => f p.2 * g (p.2 - circleMap x r p.1)
  have hH : Integrable (fun p : ℝ × ℂ => 1 * (B * |g (p.2 - circleMap x r p.1)|)) (μI.prod volume) :=
    hminus.integrable_comp_of_integrable (g := fun p : ℝ × ℂ => 1 * (B * |g p.2|))
      (h1I.mul_prod (hgi.abs.const_mul B))
  have hΦm : AEStronglyMeasurable Φ (μI.prod volume) :=
    hf.comp_snd.mul (hg.comp (continuous_snd.sub (hcm.comp continuous_fst))).aestronglyMeasurable
  have hΦ : Integrable Φ (μI.prod volume) := by
    refine hH.mono' hΦm (Eventually.of_forall fun p => ?_)
    simp only [Φ, one_mul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
  have h02 : (0 : ℝ) ≤ 2 * π := by positivity
  have hpt : ∀ t, (2 * π)⁻¹ * ∫ θ, Φ (θ, t) ∂μI = f t * circleAverage g (t - x) r := by
    intro t
    have hc : ∀ θ, t - circleMap x r θ = circleMap (t - x) (-r) θ := by
      intro θ
      rw [circleMap_neg_radius_eq_sub, circleMap_eq_add_circleMap_zero x]
      ring
    rw [← circleAverage_neg_radius]
    simp only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h02, μI, Set.uIoc_of_le h02,
      Φ, hc, integral_const_mul]
    ring
  refine ⟨intervalIntegrable_iff.2 hΦ.integral_prod_left, ?_, ?_⟩
  · exact (hΦ.integral_prod_right.const_mul (2 * π)⁻¹).congr (Eventually.of_forall hpt)
  · simp_rw [← hpt]
    rw [integral_const_mul, ← integral_prod_symm _ hΦ, integral_prod _ hΦ, circleAverage_def, smul_eq_mul,
      intervalIntegral.integral_of_le h02]
    simp only [μI, Set.uIoc_of_le h02, Φ]

/-! ## Superharmonic functions have nonpositive distributional Laplacian -/

/-- **Converse of Weyl's lemma (superharmonic form).** A function continuous and classically superharmonic on an
open set `U` satisfies `Δw ≤ 0` on `U` in the distributional sense. Proof: for a nonnegative test function `φ` and
`w̃ = 1_S w` (`S` a closed neighbourhood of `supp φ` in `U`),
`∫ w̃ (M(φ; ·, r) - φ) = ∫ φ (M(w̃; ·, r) - w̃) ≤ 0` (`integral_mul_circleAverage_comm`), and
`2π (M(φ; ·, r) - φ) / κ_r → Δφ` uniformly as `r → 0` (`abs_circleAverage_sub_sub_le`). -/
theorem laplacianLEOfSuperharmonicStep_holds : LaplacianLEOfSuperharmonicStep := by
  intro U w hU hw hsup
  refine ⟨hw.locallyIntegrableOn hU.measurableSet, fun φ hφ hφ0 _ => ?_⟩
  rw [integral_zero_measure]
  obtain ⟨hφs, hφc, hφU⟩ := hφ
  have hφ2 : ContDiff ℝ 2 φ := hφs.of_le (by norm_num)
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff hφ2
  have hΔs : HasCompactSupport (Δ φ) := hasCompactSupport_laplacian hφc
  obtain ⟨CΔ, hCΔ⟩ := hΔc.bounded_above_of_compact_support hΔs
  obtain ⟨Cφ, hCφ⟩ := hφs.continuous.bounded_above_of_compact_support hφc
  obtain ⟨δ, hδ, hδU⟩ := hφc.isCompact.exists_cthickening_subset_open hU hφU
  set S := cthickening δ (tsupport φ)
  have hScpt : IsCompact S := hφc.isCompact.cthickening
  have hSm : MeasurableSet S := isClosed_cthickening.measurableSet
  set w' : ℂ → ℝ := S.indicator w
  have hwS : ContinuousOn w S := hw.mono hδU
  obtain ⟨Bw, hBw⟩ := hScpt.exists_bound_of_continuousOn hwS
  have hBw' : ∀ y, |w' y| ≤ max Bw 0 := by
    intro y
    by_cases hy : y ∈ S
    · rw [show w' y = w y from indicator_of_mem hy w]
      exact (by simpa [Real.norm_eq_abs] using hBw y hy : |w y| ≤ Bw).trans (le_max_left _ _)
    · simp only [w', indicator_of_notMem hy, abs_zero]
      exact le_max_right _ _
  have hw'i : Integrable w' := (hwS.integrableOn_compact hScpt).integrable_indicator hSm
  have hw'm : AEStronglyMeasurable w' volume := hw'i.aestronglyMeasurable
  have hw'φ : Integrable (fun y => φ y * w' y) :=
    hw'i.bdd_mul hφs.continuous.aestronglyMeasurable (Eventually.of_forall hCφ)
  have hw'Δ : Integrable (fun y => Δ φ y * w' y) :=
    hw'i.bdd_mul hΔc.aestronglyMeasurable (Eventually.of_forall hCΔ)
  -- `w` may be replaced by `w̃ = 1_S w`
  have ha : ∫ x, w x * Δ φ x = ∫ x, w' x * Δ φ x := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    by_cases hy : y ∈ tsupport φ
    · rw [show w' y = w y from indicator_of_mem (self_subset_cthickening _ hy) w]
    · simp only [laplacian_eq_zero_of_notMem_tsupport hy, mul_zero]
  rw [ha]
  -- the circle-average inequality
  have hb : ∀ r, 0 < r → r ≤ δ → Integrable (fun y => w' y * (2 * π * (circleAverage φ y r - φ y))) ∧
      ∫ y, w' y * (2 * π * (circleAverage φ y r - φ y)) ≤ 0 := by
    intro r hr hrδ
    obtain ⟨hi1, hi2, heq⟩ := integral_mul_circleAverage_comm hw'm hBw' hφs.continuous hφc r
    have hi3 : Integrable (fun y => w' y * φ y) := by simpa only [mul_comm] using hw'φ
    have hI : Integrable (fun y => w' y * (2 * π * (circleAverage φ y r - φ y))) :=
      ((hi1.sub hi3).const_mul (2 * π)).congr (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)
    refine ⟨hI, ?_⟩
    have hrw : ∫ y, w' y * (2 * π * (circleAverage φ y r - φ y)) =
        2 * π * ∫ y, φ y * (circleAverage w' y r - w' y) := by
      calc ∫ y, w' y * (2 * π * (circleAverage φ y r - φ y))
          = 2 * π * ((∫ y, w' y * circleAverage φ y r) - ∫ y, w' y * φ y) := by
            rw [← integral_sub hi1 hi3, ← integral_const_mul]
            congr 1; ext y; ring
        _ = 2 * π * ((∫ y, φ y * circleAverage w' y r) - ∫ y, φ y * w' y) := by
            rw [heq]; congr 2; congr 1; ext y; ring
        _ = 2 * π * ∫ y, φ y * (circleAverage w' y r - w' y) := by
            rw [← integral_sub hi2 hw'φ]
            congr 2; ext y; ring
    rw [hrw]
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (integral_nonpos fun y => ?_)
    by_cases hy : y ∈ tsupport φ
    · have hball : closedBall y r ⊆ S :=
        (closedBall_subset_closedBall hrδ).trans (closedBall_subset_cthickening hy δ)
      have hyS : y ∈ S := hball (mem_closedBall_self hr.le)
      have hM : circleAverage w' y r = circleAverage w y r := by
        refine circleAverage_congr_sphere fun z hz => ?_
        rw [abs_of_pos hr] at hz
        exact indicator_of_mem (hball (sphere_subset_closedBall hz)) w
      rw [hM, show w' y = w y from indicator_of_mem hyS w]
      exact mul_nonpos_of_nonneg_of_nonpos (hφ0 y)
        (sub_nonpos.2 (hsup.2 y (hδU hyS) r hr (hball.trans hδU)).2)
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact le_rfl
  -- uniform second-order expansion and conclusion
  have hc : ∀ ε, 0 < ε → ∫ y, w' y * Δ φ y ≤ ε * ∫ y, |w' y| := by
    intro ε hε
    obtain ⟨r0, hr0, hunif⟩ :=
      Metric.uniformContinuous_iff.1 (hΔs.uniformContinuous_of_continuous hΔc) ε hε
    set r := min r0 δ
    have hr : 0 < r := lt_min hr0 hδ
    set κ := ∫ v : ℂ, log⁺ (r / ‖v‖)
    have hκ : 0 < κ := integral_posLog_div_norm_pos hr
    have hest : ∀ y, |2 * π * (circleAverage φ y r - φ y) - κ * Δ φ y| ≤ ε * κ := by
      intro y
      refine abs_circleAverage_sub_sub_le hφ2 hφc hr y fun v hv => ?_
      have hd : dist (v + y) y < r0 := by
        rw [dist_eq_norm, add_sub_cancel_right]; exact hv.trans_le (min_le_left _ _)
      exact (Real.dist_eq _ _ ▸ hunif hd).le
    obtain ⟨hI, hle⟩ := hb r hr (min_le_right _ _)
    have hmono : ∫ y, w' y * (κ * Δ φ y) ≤
        ∫ y, (w' y * (2 * π * (circleAverage φ y r - φ y)) + ε * κ * |w' y|) := by
      refine integral_mono ((hw'Δ.const_mul κ).congr (Eventually.of_forall fun y => by ring))
        (hI.add (hw'i.abs.const_mul _)) fun y => ?_
      have h1 := hest y
      have h2 : w' y * (κ * Δ φ y - 2 * π * (circleAverage φ y r - φ y)) ≤ |w' y| * (ε * κ) :=
        (le_abs_self _).trans (by rw [abs_mul, abs_sub_comm]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      dsimp only
      linarith
    rw [integral_add hI (hw'i.abs.const_mul _), integral_const_mul] at hmono
    have hmono' : κ * ∫ y, w' y * Δ φ y ≤ κ * (ε * ∫ y, |w' y|) := by
      rw [← integral_const_mul]
      calc ∫ y, κ * (w' y * Δ φ y) = ∫ y, w' y * (κ * Δ φ y) := by congr 1; ext y; ring
        _ ≤ _ := hmono
        _ ≤ 0 + ε * κ * ∫ y, |w' y| := by gcongr
        _ = κ * (ε * ∫ y, |w' y|) := by ring
    exact le_of_mul_le_mul_left hmono' hκ
  set A := ∫ y, w' y * Δ φ y
  set I := ∫ y, |w' y|
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  by_contra hcon
  push Not at hcon
  have h := hc (A / (I + 1)) (div_pos hcon (by linarith))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)] at h
  nlinarith

/-! ## Weyl's lemma, superharmonic form -/

/-- **Weyl's lemma, superharmonic form (I4).** A function `w` continuous on an open set `U` with `Δw ≤ 0` on `U` in
the distributional sense is superharmonic on `U` in the classical sense: `M(w; x, r) ≤ w(x)` whenever
`closedBall x r ⊆ U`. Proof: with `w̃ = 1_S w` (`S = closedBall x (r + δ) ⊆ U`) and a normalized bump `ρ_ε`, the
mollification `u(z) = ∫ w̃(t) ρ_ε(t - z) dt` satisfies
`2π (M(u; x, r) - u(x)) = ∫ log⁺ (r / |v|) ⟨w, Δρ_ε(· - (x - v))⟩ dv ≤ 0` (`circleAverage_integral_mul_sub`,
`integral_posLog_mul_laplacian_add`, Fubini, and the hypothesis tested against `ρ_ε(· - (x - v))`), and `u → w`
uniformly on `closedBall x r` as `ε → 0`. -/
theorem superharmonicOfLaplacianLEStep_holds : SuperharmonicOfLaplacianLEStep := by
  intro U w hU hw hlap
  refine ⟨hw.lowerSemicontinuousOn, fun x hx r hr hball => ?_⟩
  have hwi : CircleIntegrable w x r :=
    ContinuousOn.circleIntegrable hr.le (hw.mono (sphere_subset_closedBall.trans hball))
  refine ⟨hwi, ?_⟩
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hU hball
  rw [cthickening_closedBall hδ.le hr.le] at hδU
  set S := closedBall x (δ + r)
  have hScpt : IsCompact S := isCompact_closedBall x (δ + r)
  have hSm : MeasurableSet S := measurableSet_closedBall
  set w' : ℂ → ℝ := S.indicator w
  have hwS : ContinuousOn w S := hw.mono hδU
  obtain ⟨Bw, hBw⟩ := hScpt.exists_bound_of_continuousOn hwS
  have hBw' : ∀ y, |w' y| ≤ max Bw 0 := by
    intro y
    by_cases hy : y ∈ S
    · rw [show w' y = w y from indicator_of_mem hy w]
      exact (by simpa [Real.norm_eq_abs] using hBw y hy : |w y| ≤ Bw).trans (le_max_left _ _)
    · simp only [w', indicator_of_notMem hy, abs_zero]
      exact le_max_right _ _
  have hw'i : Integrable w' := (hwS.integrableOn_compact hScpt).integrable_indicator hSm
  have hw'm : AEStronglyMeasurable w' volume := hw'i.aestronglyMeasurable
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨ε0, hε0, hunif⟩ :=
    Metric.uniformContinuousOn_iff.1 (hScpt.uniformContinuousOn_of_continuous hwS) (η / 2) (half_pos hη)
  set ε := min ε0 δ / 2
  have hε : 0 < ε := half_pos (lt_min hε0 hδ)
  have hεδ : ε < δ := by have := min_le_right ε0 δ; simp only [ε]; linarith [lt_min hε0 hδ]
  have hεε0 : ε < ε0 := by have := min_le_left ε0 δ; simp only [ε]; linarith [lt_min hε0 hδ]
  let ρ : ContDiffBump (0 : ℂ) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  obtain ⟨ρn, hρc, hρs, hρ0, hρ1, hρsupp⟩ : ∃ ρn : ℂ → ℝ, ContDiff ℝ ∞ ρn ∧ HasCompactSupport ρn ∧
      (∀ v, 0 ≤ ρn v) ∧ ∫ v, ρn v = 1 ∧ Function.support ρn = ball 0 ε :=
    ⟨ρ.normed volume, ρ.contDiff_normed, ρ.hasCompactSupport_normed, fun v => ρ.nonneg_normed v,
      ρ.integral_normed, ρ.support_normed_eq⟩
  have hρi : Integrable ρn := hρc.continuous.integrable_of_hasCompactSupport hρs
  set u : ℂ → ℝ := fun z => ∫ t, w' t * ρn (t - z)
  -- `u` is uniformly close to `w` on `closedBall x r`
  have hB : ∀ z ∈ closedBall x r, |u z - w z| ≤ η / 2 := by
    intro z hz
    have hzS : z ∈ S := closedBall_subset_closedBall (by linarith) hz
    have hρz : Integrable (fun t => ρn (t - z)) := hρi.comp_sub_right z
    have hint1 : ∫ t, ρn (t - z) = 1 := by
      rw [integral_sub_right_eq_self (fun t => ρn t) z]; exact hρ1
    have hw'ρ : Integrable (fun t => w' t * ρn (t - z)) := hρz.bdd_mul hw'm (Eventually.of_forall hBw')
    have hrw : u z - w z = ∫ t, (w' t - w z) * ρn (t - z) := by
      calc u z - w z = (∫ t, w' t * ρn (t - z)) - ∫ t, w z * ρn (t - z) := by
            rw [integral_const_mul, hint1, mul_one]
        _ = ∫ t, (w' t - w z) * ρn (t - z) := by
            rw [show (fun t => (w' t - w z) * ρn (t - z)) = fun t => w' t * ρn (t - z) - w z * ρn (t - z)
              from funext fun t => sub_mul _ _ _]
            exact (integral_sub hw'ρ (hρz.const_mul (w z))).symm
    rw [hrw]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ t, |(w' t - w z) * ρn (t - z)| ≤ ∫ t, η / 2 * ρn (t - z) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _) (hρz.const_mul _)
            (Eventually.of_forall fun t => ?_)
          dsimp only
          rw [abs_mul, abs_of_nonneg (hρ0 _)]
          by_cases ht : ρn (t - z) = 0
          · rw [ht, mul_zero, mul_zero]
          · have ht' : t - z ∈ ball (0 : ℂ) ε := hρsupp ▸ ht
            rw [mem_ball, dist_zero_right] at ht'
            have htS : t ∈ S := by
              rw [mem_closedBall] at hz ⊢
              calc dist t x ≤ dist t z + dist z x := dist_triangle _ _ _
                _ ≤ δ + r := by rw [dist_eq_norm]; linarith
            rw [show w' t = w t from indicator_of_mem htS w]
            refine mul_le_mul_of_nonneg_right ?_ (hρ0 _)
            have := hunif t htS z hzS (by rw [dist_eq_norm]; linarith)
            rw [Real.dist_eq] at this
            exact this.le
      _ = η / 2 := by rw [integral_const_mul, hint1, mul_one]
  -- the super-mean-value inequality for `u`
  obtain ⟨hui, hMi, hMu⟩ := circleAverage_integral_mul_sub hw'm hBw' hρc.continuous hρs x r
  have hA : circleAverage u x r ≤ u x := by
    have hMu' : circleAverage u x r = ∫ t, w' t * circleAverage ρn (t - x) r := hMu
    have hρ2 : ContDiff ℝ 2 ρn := hρc.of_le (by norm_num)
    have hux : Integrable (fun t => w' t * ρn (t - x)) :=
      (hρi.comp_sub_right x).bdd_mul hw'm (Eventually.of_forall hBw')
    have hk := integrable_posLog_div_norm hr
    obtain ⟨CΔ, hCΔ⟩ := (continuous_laplacian_of_contDiff hρ2).bounded_above_of_compact_support
      (hasCompactSupport_laplacian hρs)
    have h2π : 2 * π * (circleAverage u x r - u x) =
        ∫ t, w' t * ∫ v, log⁺ (r / ‖v‖) * Δ ρn (v + (t - x)) := by
      rw [hMu', show u x = ∫ t, w' t * ρn (t - x) from rfl, ← integral_sub hMi hux, ← integral_const_mul]
      congr 1; ext t
      rw [integral_posLog_mul_laplacian_add hρ2 hρs (t - x) hr]; ring
    set F : ℂ → ℂ → ℝ := fun t v => w' t * (log⁺ (r / ‖v‖) * Δ ρn (v + (t - x)))
    have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
      refine Integrable.mono' (hw'i.abs.mul_prod (hk.const_mul CΔ)) ?_ (Eventually.of_forall fun p => ?_)
      · refine hw'm.comp_fst.mul (Measurable.aestronglyMeasurable ?_)
        exact (continuous_posLog.measurable.comp (measurable_const.div (measurable_norm.comp measurable_snd))).mul
          ((continuous_laplacian_of_contDiff hρ2).comp
            (continuous_snd.add (continuous_fst.sub continuous_const))).measurable
      · simp only [Function.uncurry, F, norm_mul, Real.norm_eq_abs, abs_of_nonneg posLog_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCΔ _) posLog_nonneg
    have hswap : ∫ t, w' t * ∫ v, log⁺ (r / ‖v‖) * Δ ρn (v + (t - x)) =
        ∫ v, log⁺ (r / ‖v‖) * ∫ t, w' t * Δ ρn (t - (x - v)) := by
      rw [show (fun t => w' t * ∫ v, log⁺ (r / ‖v‖) * Δ ρn (v + (t - x))) = fun t => ∫ v, F t v
        from funext fun t => (integral_const_mul _ _).symm, integral_integral_swap hF]
      congr 1; ext v
      rw [← integral_const_mul]; congr 1; ext t
      simp only [F]
      rw [show v + (t - x) = t - (x - v) by ring]
      ring
    have hle : ∫ v, log⁺ (r / ‖v‖) * ∫ t, w' t * Δ ρn (t - (x - v)) ≤ 0 := by
      refine integral_nonpos fun v => ?_
      by_cases hv : ‖v‖ < r
      · refine mul_nonpos_of_nonneg_of_nonpos posLog_nonneg ?_
        have hψsupp : Function.support (fun t => ρn (t - (x - v))) ⊆ ball (x - v) ε := by
          intro t ht
          have h' : t - (x - v) ∈ ball (0 : ℂ) ε := hρsupp ▸ ht
          rwa [mem_ball, dist_zero_right, ← dist_eq_norm, ← mem_ball] at h'
        have htsupp : tsupport (fun t => ρn (t - (x - v))) ⊆ closedBall (x - v) ε :=
          closure_minimal (hψsupp.trans ball_subset_closedBall) isClosed_closedBall
        have htS : closedBall (x - v) ε ⊆ S := by
          intro t ht
          rw [mem_closedBall] at ht ⊢
          calc dist t x ≤ dist t (x - v) + dist (x - v) x := dist_triangle _ _ _
            _ ≤ δ + r := by
              rw [dist_eq_norm (x - v) x, show x - v - x = -v by ring, norm_neg]; linarith
        have hψ : IsTestFunction U (fun t => ρn (t - (x - v))) :=
          ⟨hρc.comp (contDiff_id.sub contDiff_const),
            (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsupp,
            htsupp.trans (htS.trans hδU)⟩
        have h := hlap.2 _ hψ (fun t => hρ0 _) integrable_zero_measure
        rw [integral_zero_measure] at h
        simp_rw [laplacian_comp_sub_const] at h
        calc ∫ t, w' t * Δ ρn (t - (x - v)) = ∫ t, w t * Δ ρn (t - (x - v)) := by
              refine integral_congr_ae (Eventually.of_forall fun t => ?_)
              dsimp only
              by_cases ht : t ∈ tsupport (fun t => ρn (t - (x - v)))
              · rw [show w' t = w t from indicator_of_mem (htS (htsupp ht)) w]
              · rw [← laplacian_comp_sub_const, laplacian_eq_zero_of_notMem_tsupport ht, mul_zero, mul_zero]
          _ ≤ 0 := h
      · rw [posLog_div_norm_eq_zero hr.le (not_lt.1 hv), zero_mul]
        exact le_rfl
    have h3 : 2 * π * (circleAverage u x r - u x) ≤ 0 := by rw [h2π, hswap]; exact hle
    by_contra hc
    push Not at hc
    have := mul_pos (by positivity : (0 : ℝ) < 2 * π) (sub_pos.2 hc)
    linarith
  have h1 : circleAverage (w - u) x r ≤ η / 2 := by
    refine circleAverage_mono_on_of_le_circle (hwi.sub hui) fun z hz => ?_
    rw [abs_of_pos hr] at hz
    have := hB z (sphere_subset_closedBall hz)
    simp only [Pi.sub_apply]
    linarith [neg_abs_le (u z - w z)]
  rw [circleAverage_sub hwi hui] at h1
  have h2 := hB x (mem_closedBall_self hr.le)
  linarith [le_abs_self (u x - w x)]

/-! ## The obstacle at the pole; `Δw ≤ 0` and `Δw ≥ 0` give `Δw = 0` -/

/-- Near the pole `z`, the obstacle's Green part satisfies the logarithmic lower bound of `G_{B_R}(z, ·)`:
for `0 < ‖x - z‖ < r := (R - ‖z‖)/3` one has `-t G_{B_R}(z,x) ≤ t (2π)⁻¹ (log ‖x - z‖ - log r)`. -/
theorem neg_mul_greenFunction_ball_le {R : ℝ} {z x : ℂ} {t : ℝ} (ht : 0 < t)
    (hx₀ : 0 < ‖x - z‖) (hx : ‖x - z‖ < (R - ‖z‖) / 3) :
    -t * greenFunction (ball (0 : ℂ) R) z x ≤
      t * (2 * Real.pi)⁻¹ * (Real.log ‖x - z‖ - Real.log ((R - ‖z‖) / 3)) := by
  set r := (R - ‖z‖) / 3 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  have hsub : closedBall x r ⊆ ball (0 : ℂ) R := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_zero_right]
    have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x - z‖ + ‖z‖ := by
      calc ‖y‖ = ‖(y - x) + (x - z) + z‖ := by congr 1; ring
        _ ≤ ‖(y - x) + (x - z)‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖y - x‖ + ‖x - z‖ + ‖z‖ := by gcongr; exact norm_add_le _ _
    rw [hr_def] at hy hx
    linarith
  have hxz : ‖z - x‖ = ‖x - z‖ := norm_sub_rev z x
  have hlog := log_div_le_greenFunction (O := ball (0 : ℂ) R) (isBounded_ball) (x := z) (y := x)
    hr hsub (by rw [hxz]; exact hx₀) (by rw [hxz]; exact hx)
  rw [hxz, Real.log_div hr.ne' hx₀.ne'] at hlog
  have : 0 ≤ t := ht.le
  nlinarith [mul_le_mul_of_nonneg_left hlog ht.le]

/-- **Shared step (the obstacle at the pole).** If `q_{B_R}` is continuous on the closed ball, the obstacle
`β_t = -t G_{B_R}(z, ·) + q_{B_R}` tends to `-∞` at the pole `z`. -/
theorem obstacleTendstoAtBotStep_holds : ObstacleTendstoAtBotStep := by
  intro μ R z t hR hz ht hcont
  have hz' : ‖z‖ < R := by simpa using hz
  have hr : 0 < (R - ‖z‖) / 3 := by linarith
  have hc : 0 < t * (2 * Real.pi)⁻¹ := by positivity
  have hnorm : Tendsto (fun x : ℂ => ‖x - z‖) (𝓝[≠] z) (𝓝[>] 0) := tendsto_norm_sub_self_nhdsNE z
  have hlog : Tendsto (fun x : ℂ => Real.log ‖x - z‖) (𝓝[≠] z) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hnorm
  have hg : Tendsto (fun x : ℂ => t * (2 * Real.pi)⁻¹ * (Real.log ‖x - z‖ - Real.log ((R - ‖z‖) / 3)))
      (𝓝[≠] z) atBot := by
    have h1 : Tendsto (fun x : ℂ => Real.log ‖x - z‖ - Real.log ((R - ‖z‖) / 3)) (𝓝[≠] z) atBot :=
      tendsto_atBot_add_const_right _ _ hlog
    exact h1.const_mul_atBot hc
  have hq : Tendsto (greenPotentialBall μ R) (𝓝[≠] z) (𝓝 (greenPotentialBall μ R z)) := by
    have hmem : closedBall (0 : ℂ) R ∈ 𝓝 z := mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
    exact ((hcont.continuousAt hmem).tendsto).mono_left nhdsWithin_le_nhds
  have hsum := hg.atBot_add hq
  refine tendsto_atBot_mono' _ ?_ hsum
  have hev : ∀ᶠ x in 𝓝[≠] z, 0 < ‖x - z‖ ∧ ‖x - z‖ < (R - ‖z‖) / 3 := by
    have := hnorm.eventually (Ioo_mem_nhdsGT hr)
    exact this.mono fun x hx => hx
  filter_upwards [hev] with x hx
  have := neg_mul_greenFunction_ball_le (R := R) (z := z) (x := x) ht hx.1 hx.2
  simp only [obstacle]
  linarith

/-- A smooth cut-off: for `K` compact inside the open set `U` there is `χ : ℂ → ℝ` smooth with compact support
`tsupport χ ⊆ U`, `0 ≤ χ ≤ 1`, and `χ = 1` on `K`. -/
theorem exists_cutoff_of_isCompact_subset_isOpen {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ x ∈ K, χ x = 1 := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨f, hf, hrange, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVo hK.isClosed hKV
  have hts : tsupport f = closure V := by rw [tsupport, hsupp]
  refine ⟨f, hf, ?_, hts ▸ hVU, fun x => ?_, fun x hx => (hone x).1 hx⟩
  · rw [HasCompactSupport, hts]; exact hVc
  · exact hrange (mem_range_self x)

/-- Sums, differences and scalar multiples of test functions on `U` which are built from `χ` and `φ`:
if `χ` and `φ` are test functions on `U`, so is `c * χ + s * φ` for any real `c, s`. -/
theorem IsTestFunction.const_mul_add_const_mul {U : Set ℂ} {χ φ : ℂ → ℝ} (hχ : IsTestFunction U χ)
    (hφ : IsTestFunction U φ) (c s : ℝ) : IsTestFunction U (fun x => c * χ x + s * φ x) := by
  obtain ⟨hχd, hχc, hχU⟩ := hχ
  obtain ⟨hφd, hφc, hφU⟩ := hφ
  have hK : IsCompact (tsupport χ ∪ tsupport φ) := hχc.union hφc
  have hsub : Function.support (fun x => c * χ x + s * φ x) ⊆ tsupport χ ∪ tsupport φ := by
    intro x hx
    by_contra hx'
    rw [mem_union, not_or] at hx'
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hx'.1, image_eq_zero_of_notMem_tsupport hx'.2])
  refine ⟨(hχd.const_smul c |>.add (hφd.const_smul s)), ?_, ?_⟩
  · exact HasCompactSupport.intro hK fun x hx => by
      by_contra h
      exact hx (hsub (Function.mem_support.2 h))
  · exact (closure_minimal hsub (isClosed_tsupport χ |>.union (isClosed_tsupport φ))).trans
      (union_subset hχU hφU)

/-- For a locally integrable `w` on `U` and a test function `ψ` on `U`, `w Δψ` is integrable. -/
theorem integrable_mul_laplacian {U : Set ℂ} {w : ℂ → ℝ} (hw : LocallyIntegrableOn w U) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction U ψ) : Integrable (fun x => w x * Δ ψ x) := by
  obtain ⟨hψd, hψc, hψU⟩ := hψ
  have hwK : IntegrableOn w (tsupport ψ) := hw.integrableOn_compact_subset hψU hψc
  have hcont : Continuous (Δ ψ) := continuous_laplacian_of_contDiff (hψd.of_le (by norm_num))
  have h := hwK.mul_continuousOn hcont.continuousOn hψc
  refine h.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  simp [laplacian_eq_zero_of_notMem_tsupport hx]

/-- **Shared step.** On an open set `U`, `Δw ≤ 0` and `Δw ≥ 0` (tested against nonnegative test functions) give
`Δw = 0` against all test functions (`HasLaplacian w 0 0 U`). -/
theorem hasLaplacianOfLaplacianLEGEStep_holds : HasLaplacianOfLaplacianLEGEStep := by
  intro U w hU hLE hGE
  refine ⟨hLE.1, fun φ hφ => ⟨integrable_zero_measure, integrable_zero_measure, ?_⟩⟩
  simp only [integral_zero_measure, sub_self]
  obtain ⟨hφd, hφc, hφU⟩ := hφ
  have hφ' : IsTestFunction U φ := ⟨hφd, hφc, hφU⟩
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hφc hU hφU
  have hχ' : IsTestFunction U χ := ⟨hχd, hχc, hχU⟩
  obtain ⟨C, hC⟩ := hφd.continuous.bounded_above_of_compact_support hφc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- the two test functions `C χ + φ` and `C χ - φ`
  have hpos : ∀ s : ℝ, |s| ≤ 1 → ∀ x, 0 ≤ C * χ x + s * φ x := by
    intro s hs x
    by_cases hx : x ∈ tsupport φ
    · rw [hχ1 x hx]
      have := hC x
      rw [Real.norm_eq_abs] at this
      have h2 : |s * φ x| ≤ C := by
        rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg (φ x)]
      linarith [neg_abs_le (s * φ x)]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      nlinarith [(hχ01 x).1]
  have hL : ∀ s : ℝ, |s| ≤ 1 → ∫ x, w x * Δ (fun y => C * χ y + s * φ y) x = 0 := by
    intro s hs
    have hT := hχ'.const_mul_add_const_mul hφ' C s
    have h1 := hLE.2 _ hT (hpos s hs) integrable_zero_measure
    have h2 := (hGE.2 _ hT (hpos s hs)).2
    simp only [integral_zero_measure] at h1 h2
    exact le_antisymm h1 h2
  have hlin : ∀ s : ℝ, ∫ x, w x * Δ (fun y => C * χ y + s * φ y) x =
      C * (∫ x, w x * Δ χ x) + s * ∫ x, w x * Δ φ x := by
    intro s
    have e : (fun x => w x * Δ (fun y => C * χ y + s * φ y) x) =
        fun x => C * (w x * Δ χ x) + s * (w x * Δ φ x) := by
      funext x
      have h2 : ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → ContDiffAt ℝ 2 f x := fun f hf =>
        (hf.of_le (by norm_num)).contDiffAt
      have hCχ : Δ (fun y => C * χ y) x = C * Δ χ x := by
        have := InnerProductSpace.laplacian_smul (𝕜 := ℝ) (f := χ) (x := x) C (h2 χ hχd)
        exact this
      have hsφ : Δ (fun y => s * φ y) x = s * Δ φ x := by
        have := InnerProductSpace.laplacian_smul (𝕜 := ℝ) (f := φ) (x := x) s (h2 φ hφd)
        exact this
      have hadd : Δ (fun y => C * χ y + s * φ y) x =
          Δ (fun y => C * χ y) x + Δ (fun y => s * φ y) x :=
        ContDiffAt.laplacian_add (f₁ := fun y => C * χ y) (f₂ := fun y => s * φ y)
          ((h2 χ hχd).const_smul C) ((h2 φ hφd).const_smul s)
      rw [hadd, hCχ, hsφ]; ring
    rw [e, integral_add ((integrable_mul_laplacian hLE.1 hχ').const_mul C)
      ((integrable_mul_laplacian hLE.1 hφ').const_mul s), integral_const_mul, integral_const_mul]
  have h1 := hL 1 (by simp)
  have h2 := hL (-1) (by simp)
  rw [hlin] at h1 h2
  linarith

end HarmonicBalls

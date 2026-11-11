import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Defs.GFF
import HarmonicBalls.FirstPass.Frozen.S11aj
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Derivation of the frozen Cameron-Martin reweighting input (phase 2, worker z7)

Derives `HarmonicBalls.S11aj.CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:33`), exactly as typed,
as a theorem without hypotheses. Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9 and its
Gaussian-tilting proof, with the normalization and joint-observable verification supplied here.

Route (notes/fp-gaps/CHATGPT-lh-R7-cameron-martin.md, section 2): with `q_f = -(2π)⁻¹ Δ f`, `X = hC(q_f)`,
`v = Var X`, the tilt `dP'/dP = exp(-X - v/2)` shifts every observable `Y_o` by `a_o = o.smear f`, because
`Cov(Y_o, X) = a_o` (the log-potential identity below).

Sections:
1. Euclidean Laplacian test function `cmTestFn f = -(2π)⁻¹ Δ f`; logarithmic potential `∫ log‖x - y‖ q(y) dy = -f(x)`.
2. Circle averages of `log‖· - y‖` and the identity `∫ log⁺‖y‖ q(y) dy = -Av_{∂B_1} f`.
3. The covariance identity `∫ wholePlaneCov x y q(y) dy = f x` for `Av_{∂B_1} f = 0`.
-/

namespace HarmonicBalls.S11aj

open MeasureTheory ProbabilityTheory Metric Set Laplacian
open scoped ENNReal ContDiff

universe u

/-- The test function `q_f = -(2π)⁻¹ Δ f` (Euclidean Laplacian), with `Δ` Mathlib's `Laplacian.laplacian`. -/
noncomputable def cmTestFn (f : ℂ → ℝ) (y : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Δ f y

theorem contDiff_laplacian_of_contDiff' {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (Δ f) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  have hT : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ 2 f) := hf.iteratedFDeriv_right (by simp)
  have h1 : ∀ v : Fin 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) (fun x => iteratedFDeriv ℝ 2 f x v) := fun v =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ v).contDiff.comp hT
  exact (h1 _).add (h1 _)

theorem cmTestFn_contDiff {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (cmTestFn f) :=
  contDiff_const.mul (contDiff_laplacian_of_contDiff' hf)

theorem cmTestFn_hasCompactSupport {f : ℂ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (cmTestFn f) :=
  (hasCompactSupport_laplacian hc).mul_left

theorem cmTestFn_isTestFunction {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    IsTestFunction univ (cmTestFn f) :=
  ⟨cmTestFn_contDiff hf, cmTestFn_hasCompactSupport hc, subset_univ _⟩

/-- Logarithmic potential of `q_f`: `∫ log‖x - y‖ q_f(y) dy = -f(x)` (Newton kernel identity). -/
theorem integral_log_norm_mul_cmTestFn {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : ℂ) : ∫ y, Real.log ‖x - y‖ * cmTestFn f y = -f x := by
  have h := integral_newtonKernel_mul_laplacian (hf.of_le (by norm_num)) hc x
  rw [← h]
  congr 1
  ext y
  simp only [cmTestFn, newtonKernel]
  ring



/-- The truncated logarithm profile `w ↦ |log ‖w‖|` on `closedBall 0 (R+1)`, zero outside. -/
noncomputable def logDomProfile (R : ℝ) (w : ℂ) : ℝ :=
  (closedBall (0 : ℂ) (R + 1)).indicator (fun w => ‖Real.log ‖w‖‖) w

theorem integrable_logDomProfile (R : ℝ) : Integrable (logDomProfile R) := by
  have h0 : IntegrableOn (fun w : ℂ => ‖Real.log ‖w‖‖) (ball (0 : ℂ) (R + 2)) :=
    (integrableOn_ball_log_norm (R + 2)).norm
  have h1 : IntegrableOn (fun w : ℂ => ‖Real.log ‖w‖‖) (closedBall (0 : ℂ) (R + 1)) :=
    h0.mono_set (closedBall_subset_ball (by linarith))
  exact h1.integrable_indicator measurableSet_closedBall

theorem logDomProfile_nonneg (R : ℝ) (w : ℂ) : 0 ≤ logDomProfile R w := by
  unfold logDomProfile
  exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) w

/-- Pointwise domination of the logarithmic kernel against a bounded test function supported in `closedBall 0 R`,
uniformly over the unit circle `‖c‖ = 1`. -/
theorem norm_log_mul_le_logDomProfile {q : ℂ → ℝ} {M R : ℝ} (hM : 0 ≤ M) (hqM : ∀ y, ‖q y‖ ≤ M)
    (hqR : ∀ y, R < ‖y‖ → q y = 0) {c : ℂ} (hc : ‖c‖ = 1) (y : ℂ) :
    ‖Real.log ‖c - y‖ * q y‖ ≤ M * logDomProfile R (c - y) := by
  by_cases h : ‖c - y‖ ≤ R + 1
  · have hmem : c - y ∈ closedBall (0 : ℂ) (R + 1) := by
      rw [mem_closedBall_zero_iff]; exact h
    have hΦ : logDomProfile R (c - y) = ‖Real.log ‖c - y‖‖ := by
      unfold logDomProfile; exact Set.indicator_of_mem hmem _
    rw [hΦ, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hqM y) (norm_nonneg _)
  · have hy : R < ‖y‖ := by
      have : ‖c - y‖ ≤ ‖c‖ + ‖y‖ := norm_sub_le _ _
      linarith [not_le.mp h]
    rw [hqR y hy, mul_zero, norm_zero]
    exact mul_nonneg hM (logDomProfile_nonneg R _)


/-- Circle average over the unit circle, unfolded to the interval integral of `f (circleMap 0 1 θ)`. -/
theorem realCircleAverage_zero_one (g : ℂ → ℝ) :
    Real.circleAverage g 0 1 = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 1 θ) := by
  rw [Real.circleAverage_def, smul_eq_mul]

/-- The circle average of `log‖· - y‖` over the unit circle is `log⁺‖y‖` (Jensen, Mathlib). -/
theorem posLog_eq_circleAverage_log (y : ℂ) :
    Real.posLog ‖y‖ = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖circleMap 0 1 θ - y‖ := by
  rw [← realCircleAverage_zero_one (fun z => Real.log ‖z - y‖), circleAverage_log_norm_sub_const_eq_posLog]

/-- **Logarithmic potential of the Gaussian test function.** `∫ log⁺‖y‖ q_f(y) dy = -Av_{∂B_1(0)} f`, obtained by
writing `log⁺‖y‖` as the circle average of `log‖· - y‖` and exchanging the order of integration. -/
theorem integral_posLog_mul_cmTestFn {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∫ y, Real.posLog ‖y‖ * cmTestFn f y = -Real.circleAverage f 0 1 := by
  have hq_cont : Continuous (cmTestFn f) := (cmTestFn_contDiff hf).continuous
  have hq_cs : HasCompactSupport (cmTestFn f) := cmTestFn_hasCompactSupport hc
  obtain ⟨M, hM⟩ := hq_cont.bounded_above_of_compact_support hq_cs
  obtain ⟨R, hR⟩ := hq_cs.isCompact.isBounded.subset_closedBall 0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hqR : ∀ y, R < ‖y‖ → cmTestFn f y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have := hR h
    rw [mem_closedBall_zero_iff] at this
    linarith
  set G : ℝ → ℂ → ℝ := fun θ y => Real.log ‖circleMap 0 1 θ - y‖ * cmTestFn f y with hGdef
  have hnorm1 : ∀ θ : ℝ, ‖circleMap (0 : ℂ) 1 θ‖ = 1 := fun θ => by simp [norm_circleMap_zero]
  have hdom : ∀ θ : ℝ, ∀ y, ‖G θ y‖ ≤ M * logDomProfile R (circleMap 0 1 θ - y) :=
    fun θ y => norm_log_mul_le_logDomProfile hM0 hM hqR (hnorm1 θ) y
  have hGmeas : Measurable (fun p : ℝ × ℂ => G p.1 p.2) := by
    apply Measurable.mul
    · apply Real.measurable_log.comp
      apply continuous_norm.measurable.comp
      apply Measurable.sub
      · exact (continuous_circleMap 0 1).measurable.comp measurable_fst
      · exact measurable_snd
    · exact hq_cont.measurable.comp measurable_snd
  have hG1 : ∀ θ : ℝ, Integrable (G θ) := by
    intro θ
    refine Integrable.mono' (((integrable_logDomProfile R).comp_sub_left (circleMap 0 1 θ)).const_mul M) ?_
      (ae_of_all _ (hdom θ))
    exact (hGmeas.comp measurable_prodMk_left).aestronglyMeasurable
  have hI2 : Integrable (fun θ : ℝ => ∫ y, ‖G θ y‖) (volume.restrict (Ioc 0 (2 * Real.pi))) := by
    have hmeasI : AEStronglyMeasurable (fun θ : ℝ => ∫ y, ‖G θ y‖) (volume.restrict (Ioc 0 (2 * Real.pi))) :=
      (hGmeas.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    refine Integrable.mono' (integrable_const (M * ∫ w, logDomProfile R w)) hmeasI ?_
    refine ae_of_all _ (fun θ => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    calc ∫ y, ‖G θ y‖ ≤ ∫ y, M * logDomProfile R (circleMap 0 1 θ - y) :=
          integral_mono (hG1 θ).norm (((integrable_logDomProfile R).comp_sub_left _).const_mul M)
            (fun y => hdom θ y)
      _ = M * ∫ w, logDomProfile R w := by
          rw [integral_const_mul, integral_sub_left_eq_self]
  have hH3 : Integrable (fun p : ℝ × ℂ => G p.1 p.2) ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) :=
    (integrable_prod_iff hGmeas.aestronglyMeasurable).2 ⟨ae_of_all _ (fun θ => hG1 θ), hI2⟩
  have hH4 : Integrable (fun p : ℂ × ℝ => G p.2 p.1) (volume.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) :=
    hH3.swap
  have hswap : ∫ y, ∫ θ in Ioc 0 (2 * Real.pi), G θ y = ∫ θ in Ioc 0 (2 * Real.pi), ∫ y, G θ y :=
    integral_integral_swap hH4
  have hint : ∀ y : ℂ, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), G θ y =
      (∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖circleMap 0 1 θ - y‖) * cmTestFn f y := by
    intro y
    rw [← intervalIntegral.integral_of_le (by positivity), ← intervalIntegral.integral_mul_const]
  have hstep1 : ∀ y : ℂ, Real.posLog ‖y‖ * cmTestFn f y =
      (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), G θ y := by
    intro y
    rw [hint y, posLog_eq_circleAverage_log y]
    ring
  have hstep3 : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ y, G θ y =
      ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), -f (circleMap 0 1 θ) := by
    refine integral_congr_ae (ae_of_all _ (fun θ => ?_))
    exact integral_log_norm_mul_cmTestFn hf hc (circleMap 0 1 θ)
  calc ∫ y, Real.posLog ‖y‖ * cmTestFn f y
      = (2 * Real.pi)⁻¹ * ∫ y, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), G θ y := by
        simp_rw [hstep1]
        rw [integral_const_mul]
    _ = (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ y, G θ y := by rw [hswap]
    _ = (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), -f (circleMap 0 1 θ) := by rw [hstep3]
    _ = -Real.circleAverage f 0 1 := by
        rw [integral_neg, realCircleAverage_zero_one, ← intervalIntegral.integral_of_le (by positivity)]
        ring


/-- Pointwise domination of `log‖c - y‖ q(y)` for `‖c‖ ≤ K`, against the profile with radius `R + K`. -/
theorem norm_log_mul_le_logDomProfile' {q : ℂ → ℝ} {M R K : ℝ} (hM : 0 ≤ M) (hqM : ∀ y, ‖q y‖ ≤ M)
    (hqR : ∀ y, R < ‖y‖ → q y = 0) {c : ℂ} (hc : ‖c‖ ≤ K) (y : ℂ) :
    ‖Real.log ‖c - y‖ * q y‖ ≤ M * logDomProfile (R + K) (c - y) := by
  by_cases h : ‖c - y‖ ≤ R + K + 1
  · have hmem : c - y ∈ closedBall (0 : ℂ) (R + K + 1) := by
      rw [mem_closedBall_zero_iff]; exact h
    have hΦ : logDomProfile (R + K) (c - y) = ‖Real.log ‖c - y‖‖ := by
      unfold logDomProfile; exact Set.indicator_of_mem hmem _
    rw [hΦ, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hqM y) (norm_nonneg _)
  · have hy : R < ‖y‖ := by
      have : ‖c - y‖ ≤ ‖c‖ + ‖y‖ := norm_sub_le _ _
      linarith [not_le.mp h]
    rw [hqR y hy, mul_zero, norm_zero]
    exact mul_nonneg hM (logDomProfile_nonneg _ _)

/-- Integrability of `y ↦ log‖c - y‖ q(y)` for a bounded measurable `q` supported in `closedBall 0 R`. -/
theorem integrable_log_sub_mul {q : ℂ → ℝ} {M R : ℝ} (hq : Measurable q) (hM : 0 ≤ M)
    (hqM : ∀ y, ‖q y‖ ≤ M) (hqR : ∀ y, R < ‖y‖ → q y = 0) (c : ℂ) :
    Integrable (fun y => Real.log ‖c - y‖ * q y) := by
  refine Integrable.mono' (((integrable_logDomProfile (R + ‖c‖)).comp_sub_left c).const_mul M) ?_
    (ae_of_all _ (fun y => norm_log_mul_le_logDomProfile' hM hqM hqR (le_refl ‖c‖) y))
  exact ((Real.measurable_log.comp (continuous_norm.measurable.comp (measurable_const.sub measurable_id))).mul
    hq).aestronglyMeasurable

/-- The logarithm of the Euclidean norm is the positive part of `log`: `log (max ‖z‖ 1) = log⁺ ‖z‖`. -/
theorem log_max_one_eq_posLog {r : ℝ} (hr : 0 ≤ r) : Real.log (max r 1) = Real.posLog r := by
  unfold Real.posLog
  rcases le_total r 1 with h | h
  · rw [max_eq_right h, Real.log_one, max_eq_left (Real.log_nonpos hr h)]
  · rw [max_eq_left h, max_eq_right (Real.log_nonneg h)]

/-- Off the diagonal the covariance kernel splits: `wholePlaneCov x y = log⁺‖x‖ + log⁺‖y‖ - log‖x - y‖`. -/
theorem wholePlaneCov_eq_of_ne {x y : ℂ} (h : y ≠ x) :
    wholePlaneCov x y = Real.posLog ‖x‖ + Real.posLog ‖y‖ - Real.log ‖x - y‖ := by
  unfold wholePlaneCov
  have hx : 0 < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hy : 0 < max ‖y‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hxy : ‖x - y‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h' => h h'.symm
  rw [Real.log_div (mul_pos hx hy).ne' hxy, Real.log_mul hx.ne' hy.ne', log_max_one_eq_posLog (norm_nonneg _),
    log_max_one_eq_posLog (norm_nonneg _)]


/-- Uniform bounds for `q_f`: bounded by `M`, vanishing outside `closedBall 0 R`. -/
theorem cmTestFn_bounds {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ M R : ℝ, 0 ≤ M ∧ (∀ y, ‖cmTestFn f y‖ ≤ M) ∧ (∀ y, R < ‖y‖ → cmTestFn f y = 0) := by
  have hq_cs : HasCompactSupport (cmTestFn f) := cmTestFn_hasCompactSupport hc
  obtain ⟨M, hM⟩ := (cmTestFn_contDiff hf).continuous.bounded_above_of_compact_support hq_cs
  obtain ⟨R, hR⟩ := hq_cs.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, R, (norm_nonneg _).trans (hM 0), hM, fun y hy => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := hR h
  rw [mem_closedBall_zero_iff] at this
  linarith

/-- **The covariance identity (1).** For `Av_{∂B_1(0)} f = 0`-free data: `∫ K(x,y) q_f(y) dy = f(x) - Av_{∂B_1} f`
for every `x`, where `K = wholePlaneCov` is the whole-plane GFF covariance kernel (eq:cov-kernel). -/
theorem integral_wholePlaneCov_mul_cmTestFn {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : ℂ) : ∫ y, wholePlaneCov x y * cmTestFn f y = f x - Real.circleAverage f 0 1 := by
  obtain ⟨M, R, hM0, hqM, hqR⟩ := cmTestFn_bounds hf hc
  have hq_cont : Continuous (cmTestFn f) := (cmTestFn_contDiff hf).continuous
  have hq_int : Integrable (cmTestFn f) :=
    hq_cont.integrable_of_hasCompactSupport (cmTestFn_hasCompactSupport hc)
  have hq0 : ∫ y, cmTestFn f y = 0 := by
    unfold cmTestFn
    rw [integral_const_mul, integral_laplacian_eq_zero (hf.of_le (by norm_num)) hc, mul_zero]
  have hpos_int : Integrable (fun y => Real.posLog ‖y‖ * cmTestFn f y) :=
    ((Real.continuous_posLog.comp continuous_norm).mul hq_cont).integrable_of_hasCompactSupport
      (cmTestFn_hasCompactSupport hc).mul_left
  have hlog_int : Integrable (fun y => Real.log ‖x - y‖ * cmTestFn f y) :=
    integrable_log_sub_mul hq_cont.measurable hM0 hqM hqR x
  have hconst_int : Integrable (fun y => Real.posLog ‖x‖ * cmTestFn f y) := hq_int.const_mul _
  calc ∫ y, wholePlaneCov x y * cmTestFn f y
      = ∫ y, (Real.posLog ‖x‖ * cmTestFn f y + Real.posLog ‖y‖ * cmTestFn f y
          - Real.log ‖x - y‖ * cmTestFn f y) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_ne_complex x] with y hy
        rw [wholePlaneCov_eq_of_ne hy]
        ring
    _ = (∫ y, Real.posLog ‖x‖ * cmTestFn f y) + (∫ y, Real.posLog ‖y‖ * cmTestFn f y)
          - ∫ y, Real.log ‖x - y‖ * cmTestFn f y := by
        have hsum : Integrable (fun y => Real.posLog ‖x‖ * cmTestFn f y + Real.posLog ‖y‖ * cmTestFn f y) :=
          hconst_int.add hpos_int
        rw [integral_sub hsum hlog_int, integral_add hconst_int hpos_int]
    _ = f x - Real.circleAverage f 0 1 := by
        rw [integral_const_mul, hq0, integral_posLog_mul_cmTestFn hf hc,
          integral_log_norm_mul_cmTestFn hf hc x]
        ring


end HarmonicBalls.S11aj

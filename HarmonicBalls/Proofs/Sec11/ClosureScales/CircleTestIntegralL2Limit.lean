import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.OpenBallDensity
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestFubiniLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageSmoothTestConvergence
import HarmonicBalls.Proofs.Sec11.ClosureScales.GaussianCircleTestIntegral
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAKernelBox

/-!
# Circle-average test integrals of the whole-plane GFF converge in `L²(P)`

Let `(hC, hcirc)` be a whole-plane Gaussian free field (`IsWholePlaneGFF`; Duplantier-Sheffield 2011, Section 3.1,
Armstrong-Kuusi-Mourrat for the log-correlated normalization) and let `φ` be a test function on `ℂ`. For the circle
average `h_r(w)` of the field, the circle-average test integral `∫ w, h_r(w) φ(w)` converges in `L²(P)` to the
pairing `(h, φ) = hC φ` as `r ↓ 0`, and along the dyadic scales `2^{-n}`.

Route. By the Fubini symmetry of circle averages (`IsWholePlaneGFF.ae_integral_circle_mul_eq_pairing_circleAverage`),
the circle-average test integral is a.s. the pairing with the smoothed test function `φ_r = circleAverage φ · r`.
Only the two fixed test observables `ψ = φ_r` and `φ` are expanded; no samplewise linearity of `hC` is used. The second
moment of `hC ψ - hC φ` is the covariance kernel `wholePlaneGFFCov` at the fixed difference `ψ - φ`
(`IsWholePlaneGFF.integral_sq_sub_pairing`). The Schur bound `abs_wholePlaneGFFCov_pairing_le` controls it by
`C_M ∫ (φ_r - φ)²` for a fixed ball `ball 0 M` containing all supports, and `∫ (φ_r - φ)² → 0` by the uniform
convergence of circle averages of the test function.

The covariance kernel `wholePlaneCov` is the logarithmic kernel of potential theory (Armitage-Gardiner) normalized by
`max(|z|, 1)`, as in `HarmonicBalls/Defs/GFF.lean`.

Scope: this is the `L²(P)` statement for each fixed test function. It is not the almost-sure dyadic limit on the
canonical distribution model, and it does not give a distribution-valued or `H^{-2}` reconstruction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls

open GaussianCircleTestIntegral

namespace CircleTestIntegralL2Limit

/-- A test function on `ℂ` vanishes outside some ball. -/
lemma exists_ball_of_test {b : ℂ → ℝ} (hb : IsTestFunction Set.univ b) :
    ∃ M : ℝ, ∀ x : ℂ, x ∉ ball (0 : ℂ) M → b x = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hb.2.1.isCompact.isBounded
  refine ⟨R + 1, fun x hx => ?_⟩
  by_contra h
  have h1 : x ∈ closedBall (0 : ℂ) R := hR (subset_tsupport b (Function.mem_support.2 h))
  simp only [mem_ball, dist_zero_right, not_lt] at hx
  simp only [mem_closedBall, dist_zero_right] at h1
  linarith

lemma measurable_wholePlaneCov_right (x : ℂ) : Measurable fun y : ℂ => wholePlaneCov x y :=
  measurable_wholePlaneCov.comp (measurable_const.prodMk measurable_id)

/-- The absolute kernel `|wholePlaneCov x ·|` is integrable on a ball containing `x`: its lower Lebesgue integral is
bounded by `kernelBoxConst M` (RouteAKernelBox). -/
lemma integrableOn_abs_wholePlaneCov_ball {M : ℝ} {x : ℂ} (hx : ‖x‖ ≤ M) :
    IntegrableOn (fun y : ℂ => |wholePlaneCov x y|) (ball (0 : ℂ) M) := by
  have hm : Measurable fun y : ℂ => ENNReal.ofReal |wholePlaneCov x y| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (measurable_wholePlaneCov_right x))
  have hfin : ∫⁻ y in ball (0 : ℂ) M, ENNReal.ofReal |wholePlaneCov x y| ≠ ⊤ :=
    ne_top_of_le_ne_top (kernelBoxConst_lt_top M).ne (lintegral_ball_ofReal_abs_wholePlaneCov_le hx)
  refine Integrable.congr (integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin)
    (ae_of_all _ fun y => ?_)
  exact ENNReal.toReal_ofReal (abs_nonneg _)

/-- The integral of `|wholePlaneCov x ·|` over a ball containing `x` is bounded uniformly in `x`. -/
lemma integral_abs_wholePlaneCov_ball_le {M : ℝ} {x : ℂ} (hx : ‖x‖ ≤ M) :
    ∫ y in ball (0 : ℂ) M, |wholePlaneCov x y| ≤ (kernelBoxConst M).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => abs_nonneg _)
    (integrableOn_abs_wholePlaneCov_ball hx).1]
  exact ENNReal.toReal_mono (kernelBoxConst_lt_top M).ne
    (lintegral_ball_ofReal_abs_wholePlaneCov_le hx)

/-- Bound on the logarithmic-potential pairing `kernelPairing b x = ∫ b(y) wholePlaneCov x y dy` (Armitage-Gardiner,
logarithmic potentials) of a function `b` bounded by `B` and supported in `ball 0 M`, uniformly in `‖x‖ ≤ M`. -/
lemma abs_kernelPairing_le {b : ℂ → ℝ} {B M : ℝ} (hB : ∀ y, |b y| ≤ B)
    (hbM : ∀ y, y ∉ ball (0 : ℂ) M → b y = 0) {x : ℂ} (hx : ‖x‖ ≤ M) :
    |kernelPairing b x| ≤ B * (kernelBoxConst M).toReal := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hint : Integrable ((ball (0 : ℂ) M).indicator fun y : ℂ => |wholePlaneCov x y|) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_abs_wholePlaneCov_ball hx)
  calc |kernelPairing b x| = |∫ y, b y * wholePlaneCov x y| := rfl
    _ ≤ ∫ y, |b y * wholePlaneCov x y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, B * (ball (0 : ℂ) M).indicator (fun y : ℂ => |wholePlaneCov x y|) y := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (hint.const_mul B)
          (ae_of_all _ fun y => ?_)
        dsimp only
        by_cases hy : y ∈ ball (0 : ℂ) M
        · rw [indicator_of_mem hy, abs_mul]
          exact mul_le_mul_of_nonneg_right (hB y) (abs_nonneg _)
        · rw [hbM y hy]
          simp [indicator_of_notMem hy]
    _ = B * ∫ y in ball (0 : ℂ) M, |wholePlaneCov x y| := by
        rw [integral_const_mul, integral_indicator measurableSet_ball]
    _ ≤ B * (kernelBoxConst M).toReal :=
        mul_le_mul_of_nonneg_left (integral_abs_wholePlaneCov_ball_le hx) hB0

/-- The kernel pairing of a test function is strongly measurable. -/
lemma stronglyMeasurable_kernelPairing {b : ℂ → ℝ} (hb : IsTestFunction Set.univ b) :
    StronglyMeasurable (kernelPairing b) := by
  have hf : StronglyMeasurable (Function.uncurry fun x y : ℂ => b y * wholePlaneCov x y) :=
    Measurable.stronglyMeasurable
      ((hb.1.continuous.measurable.comp measurable_snd).mul measurable_wholePlaneCov)
  exact hf.integral_prod_right

/-- For a test function `b` and every `x`, the function `y ↦ b y * wholePlaneCov x y` is integrable. -/
lemma integrable_mul_wholePlaneCov {b : ℂ → ℝ} (hb : IsTestFunction Set.univ b) (x : ℂ) :
    Integrable fun y : ℂ => b y * wholePlaneCov x y := by
  obtain ⟨M₀, hM₀⟩ := exists_ball_of_test hb
  obtain ⟨B, hB⟩ := hb.1.continuous.bounded_above_of_compact_support hb.2.1
  have hB' : ∀ y, |b y| ≤ B := fun y => by simpa [Real.norm_eq_abs] using hB y
  have hx : ‖x‖ ≤ max ‖x‖ M₀ := le_max_left _ _
  have hbM : ∀ y, y ∉ ball (0 : ℂ) (max ‖x‖ M₀) → b y = 0 := fun y hy =>
    hM₀ y fun h => hy (ball_subset_ball (le_max_right _ _) h)
  refine Integrable.mono' (g := (ball (0 : ℂ) (max ‖x‖ M₀)).indicator fun y => B * |wholePlaneCov x y|)
    ?_ ?_ ?_
  · exact (integrable_indicator_iff measurableSet_ball).2
      (Integrable.const_mul (integrableOn_abs_wholePlaneCov_ball hx) B)
  · exact hb.1.continuous.aestronglyMeasurable.mul (measurable_wholePlaneCov_right x).aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    by_cases hy : y ∈ ball (0 : ℂ) (max ‖x‖ M₀)
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB' y) (abs_nonneg _)
    · rw [hbM y hy, indicator_of_notMem hy]
      simp

/-- The product of two test functions with a kernel pairing is integrable. -/
lemma integrable_mul_kernelPairing {a b : ℂ → ℝ} (ha : IsTestFunction Set.univ a)
    (hb : IsTestFunction Set.univ b) :
    Integrable fun x : ℂ => a x * kernelPairing b x := by
  obtain ⟨Ma, hMa⟩ := exists_ball_of_test ha
  obtain ⟨Mb, hMb⟩ := exists_ball_of_test hb
  obtain ⟨A, hA⟩ := ha.1.continuous.bounded_above_of_compact_support ha.2.1
  obtain ⟨B, hB⟩ := hb.1.continuous.bounded_above_of_compact_support hb.2.1
  have hA' : ∀ x, |a x| ≤ A := fun x => by simpa [Real.norm_eq_abs] using hA x
  have hB' : ∀ y, |b y| ≤ B := fun y => by simpa [Real.norm_eq_abs] using hB y
  have hbM : ∀ y, y ∉ ball (0 : ℂ) (max Ma Mb) → b y = 0 := fun y hy =>
    hMb y fun h => hy (ball_subset_ball (le_max_right _ _) h)
  have hKP : ∀ x : ℂ, ‖x‖ ≤ max Ma Mb →
      |kernelPairing b x| ≤ B * (kernelBoxConst (max Ma Mb)).toReal :=
    fun x hx => abs_kernelPairing_le hB' hbM hx
  refine Integrable.mono' (g := (ball (0 : ℂ) (max Ma Mb)).indicator
    fun _ => A * (B * (kernelBoxConst (max Ma Mb)).toReal)) ?_ ?_ ?_
  · exact (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  · exact ha.1.continuous.aestronglyMeasurable.mul (stronglyMeasurable_kernelPairing hb).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    by_cases hx : x ∈ ball (0 : ℂ) (max Ma Mb)
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hA' x) (hKP x (mem_ball_zero_iff.1 hx).le) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hA' 0))
    · have hax : a x = 0 := hMa x fun h => hx (ball_subset_ball (le_max_left _ _) h)
      rw [indicator_of_notMem hx, hax]
      simp

/-- Linearity of the kernel pairing in the test function, for a difference of two test functions. -/
lemma kernelPairing_sub {ψ φ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ) (hφ : IsTestFunction Set.univ φ)
    (x : ℂ) :
    kernelPairing (fun y => ψ y - φ y) x = kernelPairing ψ x - kernelPairing φ x := by
  unfold kernelPairing
  simp only [sub_mul]
  exact integral_sub (integrable_mul_wholePlaneCov hψ x) (integrable_mul_wholePlaneCov hφ x)

/-- The difference of two test functions on `ℂ` is a test function. -/
lemma isTestFunction_univ_sub {f g : ℂ → ℝ} (hf : IsTestFunction Set.univ f)
    (hg : IsTestFunction Set.univ g) : IsTestFunction Set.univ fun x => f x - g x :=
  ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, Set.subset_univ _⟩

/-- Uniform approximation of `φ` by its circle averages as the radius tends to `0`
(`CircleTestFubini.norm_circleAverage_sub_le`, uniform continuity of the compactly supported `φ`). -/
lemma exists_radius_sup_circleAverage_sub {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → r < η → ∀ x : ℂ, |Real.circleAverage φ x r - φ x| ≤ δ := by
  obtain ⟨ε, hε, hεφ⟩ := Metric.uniformContinuous_iff.1
    (hφ.2.1.uniformContinuous_of_continuous hφ.1.continuous) δ hδ
  refine ⟨ε, hε, fun r hr hrε x => ?_⟩
  have key : ∀ θ : ℝ, ‖φ (circleMap x r θ) - φ x‖ ≤ δ := by
    intro θ
    have hd : dist (circleMap x r θ) x < ε := by
      simp [circleMap, dist_eq_norm, Complex.norm_exp_ofReal_mul_I, abs_of_pos hr, hrε]
    simpa [dist_eq_norm] using (hεφ hd).le
  have h := CircleTestFubini.norm_circleAverage_sub_le hφ.1.continuous x key
  rwa [Real.norm_eq_abs] at h

/-- The circle averages of `φ` of radius in `(0, 1]` are supported in a fixed ball, and so is `φ`. -/
lemma exists_ball_circleAverage_sub_eq_zero {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    ∃ M : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : ℂ, x ∉ ball (0 : ℂ) M →
      Real.circleAverage φ x r - φ x = 0 := by
  obtain ⟨K, hKc, hφK, hrK, -⟩ := CircleTestFubini.exists_isCompact_smooth_circleAverage hφ
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hKc.isBounded
  refine ⟨R + 1, fun r hr hr1 x hx => ?_⟩
  have hxK : x ∉ K := by
    intro hxK'
    have h1 : x ∈ closedBall (0 : ℂ) R := hR hxK'
    simp only [mem_ball, dist_zero_right, not_lt] at hx
    simp only [mem_closedBall, dist_zero_right] at h1
    linarith
  have h1 : Real.circleAverage φ x r = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun v : ℂ => Real.circleAverage φ v r)
      fun h => hxK (hrK r hr hr1 h)
  have h2 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxK (hφK h)
  rw [h1, h2, sub_zero]

/-- Second moment of a function bounded by `δ` and supported in `ball 0 M`: at most `δ² · vol(ball 0 M)`. -/
lemma integral_sq_le_of_bound {f : ℂ → ℝ} {M δ : ℝ} (hsupp : ∀ x, x ∉ ball (0 : ℂ) M → f x = 0)
    (hδ : ∀ x, |f x| ≤ δ) :
    ∫ x, f x ^ 2 ≤ δ ^ 2 * (volume (ball (0 : ℂ) M)).toReal := by
  have hint : Integrable ((ball (0 : ℂ) M).indicator fun _ : ℂ => δ ^ 2) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  calc ∫ x, f x ^ 2 ≤ ∫ x, (ball (0 : ℂ) M).indicator (fun _ : ℂ => δ ^ 2) x := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hint
          (ae_of_all _ fun x => ?_)
        by_cases hx : x ∈ ball (0 : ℂ) M
        · rw [indicator_of_mem hx]
          calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
            _ ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hδ x) 2
        · simp [indicator_of_notMem hx, hsupp x hx]
    _ = δ ^ 2 * (volume (ball (0 : ℂ) M)).toReal := by
        rw [integral_indicator_const _ measurableSet_ball, smul_eq_mul]
        exact mul_comm _ _

/-- `L²(dx)` convergence of the circle averages `φ_r = circleAverage φ · r` to `φ` as `r ↓ 0`. -/
lemma tendsto_integral_sq_circleAverage_sub {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Tendsto (fun r : ℝ => ∫ x, (Real.circleAverage φ x r - φ x) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hzero⟩ := exists_ball_circleAverage_sub_eq_zero hφ
  have hV : 0 ≤ (volume (ball (0 : ℂ) M)).toReal := ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδV⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 2 * (volume (ball (0 : ℂ) M)).toReal < ε := by
    refine ⟨Real.sqrt (ε / ((volume (ball (0 : ℂ) M)).toReal + 1)),
      Real.sqrt_pos.2 (div_pos hε (by linarith)), ?_⟩
    rw [Real.sq_sqrt (div_nonneg hε.le (by linarith)), div_mul_eq_mul_div,
      div_lt_iff₀ (by linarith)]
    nlinarith
  obtain ⟨η, hη, hbd⟩ := exists_radius_sup_circleAverage_sub hφ hδpos
  filter_upwards [Ioo_mem_nhdsGT (lt_min hη zero_lt_one)] with r hr
  have hr0 : 0 < r := hr.1
  have hrη : r < η := lt_of_lt_of_le hr.2 (min_le_left _ _)
  have hr1 : r ≤ 1 := (lt_of_lt_of_le hr.2 (min_le_right _ _)).le
  have hnn : 0 ≤ ∫ x, (Real.circleAverage φ x r - φ x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  calc ∫ x, (Real.circleAverage φ x r - φ x) ^ 2
      ≤ δ ^ 2 * (volume (ball (0 : ℂ) M)).toReal :=
        integral_sq_le_of_bound (f := fun x => Real.circleAverage φ x r - φ x)
          (fun x hx => hzero r hr0 hr1 x hx) (hbd r hr0 hrη)
    _ < ε := hδV

end CircleTestIntegralL2Limit

open CircleTestIntegralL2Limit

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Fixed two-test covariance formula.** For test functions `ψ, φ` on `ℂ`, the second moment of the difference
`hC ψ - hC φ` of two pairings of the whole-plane GFF is the covariance kernel `wholePlaneGFFCov` at the fixed test
function `ψ - φ`. No samplewise linearity of `hC` is used. -/
theorem integral_sq_sub_pairing (hgff : IsWholePlaneGFF P hC hcirc) {ψ φ : ℂ → ℝ}
    (hψ : IsTestFunction Set.univ ψ) (hφ : IsTestFunction Set.univ φ) :
    ∫ ω, (hC ω ψ - hC ω φ) ^ 2 ∂P =
      wholePlaneGFFCov (GFFObservable.pairing fun x => ψ x - φ x)
        (GFFObservable.pairing fun x => ψ x - φ x) := by
  have hX : MemLp (fun ω => hC ω ψ) 2 P := memLp_pairing hgff hψ
  have hY : MemLp (fun ω => hC ω φ) 2 P := memLp_pairing hgff hφ
  have hX0 : ∫ ω, hC ω ψ ∂P = 0 := hgff.integral_eq_zero (GFFObservable.pairing ψ) hψ
  have hY0 : ∫ ω, hC ω φ ∂P = 0 := hgff.integral_eq_zero (GFFObservable.pairing φ) hφ
  have cXY : ∫ ω, hC ω ψ * hC ω φ ∂P = ∫ x, ψ x * kernelPairing φ x := by
    rw [← covariance_eq_integral_mul hX0 hY0]
    exact hgff.covariance_eq (GFFObservable.pairing ψ) (GFFObservable.pairing φ) hψ hφ
  have cYX : ∫ ω, hC ω φ * hC ω ψ ∂P = ∫ x, φ x * kernelPairing ψ x := by
    rw [← covariance_eq_integral_mul hY0 hX0]
    exact hgff.covariance_eq (GFFObservable.pairing φ) (GFFObservable.pairing ψ) hφ hψ
  have hsymm : ∫ ω, hC ω φ * hC ω ψ ∂P = ∫ ω, hC ω ψ * hC ω φ ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  have hsw : ∫ x, φ x * kernelPairing ψ x = ∫ x, ψ x * kernelPairing φ x := by
    rw [← cYX, hsymm, cXY]
  have cXX : ∫ ω, hC ω ψ * hC ω ψ ∂P = ∫ x, ψ x * kernelPairing ψ x :=
    integral_pairing_mul_pairing hgff hψ
  have cYY : ∫ ω, hC ω φ * hC ω φ ∂P = ∫ x, φ x * kernelPairing φ x :=
    integral_pairing_mul_pairing hgff hφ
  have hXX : Integrable (fun ω => hC ω ψ * hC ω ψ) P := hX.integrable_mul hX
  have hXY : Integrable (fun ω => hC ω ψ * hC ω φ) P := hX.integrable_mul hY
  have hYY : Integrable (fun ω => hC ω φ * hC ω φ) P := hY.integrable_mul hY
  have h1 : Integrable (fun ω => hC ω ψ * hC ω ψ - 2 * (hC ω ψ * hC ω φ)) P :=
    hXX.sub (hXY.const_mul 2)
  have hexp : ∫ ω, (hC ω ψ - hC ω φ) ^ 2 ∂P
      = ∫ ω, hC ω ψ * hC ω ψ ∂P - 2 * ∫ ω, hC ω ψ * hC ω φ ∂P + ∫ ω, hC ω φ * hC ω φ ∂P := by
    have hfun : (fun ω => (hC ω ψ - hC ω φ) ^ 2)
        = fun ω => (hC ω ψ * hC ω ψ - 2 * (hC ω ψ * hC ω φ)) + hC ω φ * hC ω φ := by
      funext ω
      ring
    rw [hfun, integral_add h1 hYY, integral_sub hXX (hXY.const_mul 2), integral_const_mul]
  have hpt : ∀ x : ℂ, (ψ x - φ x) * kernelPairing (fun y => ψ y - φ y) x
      = (ψ x * kernelPairing ψ x - ψ x * kernelPairing φ x)
        - (φ x * kernelPairing ψ x - φ x * kernelPairing φ x) := by
    intro x
    rw [kernelPairing_sub hψ hφ x]
    ring
  have hRHS : wholePlaneGFFCov (GFFObservable.pairing fun x => ψ x - φ x)
      (GFFObservable.pairing fun x => ψ x - φ x)
      = ∫ x, (ψ x - φ x) * kernelPairing (fun y => ψ y - φ y) x := rfl
  have hint : ∫ x, (ψ x - φ x) * kernelPairing (fun y => ψ y - φ y) x
      = ∫ x, (ψ x * kernelPairing ψ x - ψ x * kernelPairing φ x)
        - (φ x * kernelPairing ψ x - φ x * kernelPairing φ x) :=
    integral_congr_ae (ae_of_all _ hpt)
  have k1 : Integrable (fun x : ℂ => ψ x * kernelPairing ψ x - ψ x * kernelPairing φ x) :=
    (integrable_mul_kernelPairing hψ hψ).sub (integrable_mul_kernelPairing hψ hφ)
  have k2 : Integrable (fun x : ℂ => φ x * kernelPairing ψ x - φ x * kernelPairing φ x) :=
    (integrable_mul_kernelPairing hφ hψ).sub (integrable_mul_kernelPairing hφ hφ)
  rw [hRHS, hint, integral_sub k1 k2,
    integral_sub (integrable_mul_kernelPairing hψ hψ) (integrable_mul_kernelPairing hψ hφ),
    integral_sub (integrable_mul_kernelPairing hφ hψ) (integrable_mul_kernelPairing hφ hφ),
    hexp, cXX, cYY, cXY, hsw]
  ring

/-- **`L²(P)` convergence of the circle-average test integrals.** For a test function `φ` on `ℂ` and a radius
`0 < r ≤ 1`, the difference `∫ w, h_r(w) φ(w) dw - (h, φ)` is square integrable. -/
theorem memLp_circleTestIntegral_sub (hgff : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    MemLp (fun ω => (∫ w, hcirc ω r w * φ w) - hC ω φ) 2 P := by
  have hψ : IsTestFunction Set.univ (fun v => Real.circleAverage φ v r) :=
    CircleTestFubini.isTestFunction_univ_circleAverage hφ (by rw [abs_of_pos hr]; exact hr1)
  have hL : MemLp (fun ω => hC ω (fun v => Real.circleAverage φ v r) - hC ω φ) 2 P :=
    (memLp_pairing hgff hψ).sub (memLp_pairing hgff hφ)
  refine hL.ae_eq ?_
  filter_upwards [hgff.ae_integral_circle_mul_eq_pairing_circleAverage hφ hr hr1] with ω hω
  rw [hω.2]

/-- **`L²(P)` convergence of the circle-average test integrals as `r ↓ 0`.** -/
theorem tendsto_integral_sq_circleTestIntegral_sub (hgff : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) :
    Tendsto (fun r : ℝ => ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hzero⟩ := exists_ball_circleAverage_sub_eq_zero hφ
  set C : ℝ := (2 * kernelBoxConst M).toReal with hCdef
  have hu := (tendsto_integral_sq_circleAverage_sub hφ).const_mul C
  rw [mul_zero] at hu
  refine squeeze_zero_norm' ?_ hu
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with r hr
  have hr0 : 0 < r := hr.1
  have hr1 : r ≤ 1 := hr.2.le
  have hψ : IsTestFunction Set.univ (fun v => Real.circleAverage φ v r) :=
    CircleTestFubini.isTestFunction_univ_circleAverage hφ (by rw [abs_of_pos hr0]; exact hr1)
  have hf : IsTestFunction Set.univ (fun x => Real.circleAverage φ x r - φ x) :=
    isTestFunction_univ_sub hψ hφ
  have hEq : ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P
      = ∫ ω, (hC ω (fun v => Real.circleAverage φ v r) - hC ω φ) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hgff.ae_integral_circle_mul_eq_pairing_circleAverage hφ hr0 hr1] with ω hω
    rw [hω.2]
  obtain ⟨B, hB⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2.1
  have hB' : ∀ x, |Real.circleAverage φ x r - φ x| ≤ B := fun x => by simpa [Real.norm_eq_abs] using hB x
  have hS := abs_wholePlaneGFFCov_pairing_le (M := M) (B := B)
    (f := fun x => Real.circleAverage φ x r - φ x) hf.1.continuous.measurable
    (fun x hx => hzero r hr0 hr1 x hx) hB'
  rw [hEq, integral_sq_sub_pairing hgff hψ hφ, Real.norm_eq_abs]
  exact hS

/-- **`L²(P)` convergence along the dyadic scales `2^{-n}`.** -/
theorem tendsto_integral_sq_circleTestIntegral_sub_dyadicScale (hgff : IsWholePlaneGFF P hC hcirc)
    {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Tendsto (fun n : ℕ => ∫ ω, ((∫ w, hcirc ω (dyadicScale n) w * φ w) - hC ω φ) ^ 2 ∂P)
      atTop (𝓝 0) :=
  (tendsto_integral_sq_circleTestIntegral_sub hgff hφ).comp tendsto_dyadicScale_nhdsGT

end IsWholePlaneGFF

end HarmonicBalls

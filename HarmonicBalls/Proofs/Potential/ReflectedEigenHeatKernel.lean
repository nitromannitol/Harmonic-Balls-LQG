import HarmonicBalls.Proofs.Potential.ReflectedEigenKernelTests
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelChapmanKolmogorov
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The eigenfunction kernel is a strictly positive continuous heat kernel of the time change

Let `A` be a clock of reflected Brownian motion in `K₀` whose Revuz measure `ν` is a probability
measure charging every relative ball of `K₀`, with upper power bounds, and `p` the eigenfunction
kernel of an eigenbasis of the centered Green operator. Then:

* `p ≥ 0` on `(0, ∞) × K₀ × K₀` (`eigenKernel_nonneg`): if `p(v, x, y₀) < 0`, then
  `p(v, x, ·) < p(v, x, y₀)/2` near `y₀`, and for the bump `ψ = (r - |· - y₀|)⁺` the identity
  `E_x ψ(Y_v) = ∫ p(v, x, y) ψ(y) ν(dy)` would make a nonnegative number negative;
* the law of `Y_v` under `Q_x` is `p(v, x, y) ν(dy)` (`map_clockPair_eq_withDensity`), since the
  two finite measures have the same integrals against bounded continuous functions, so `p` is a
  heat kernel of the time change from every start of `K₀` (`isLBMHeatKernel_eigenKernel`), jointly
  continuous on `(0, ∞) × K₀ × K₀`;
* `p > 0` on `(0, ∞) × K₀ × K₀` (`eigenKernel_pos`): `p(s, y, y) = 1 + ∑ e^{-λ_i s} ϕ_i(y)² ≥ 1`,
  so by the Chapman–Kolmogorov identity a positive value at `(u, x, y)` stays positive at all later
  times; a zero at `t₀` would then vanish on `(0, t₀)`, but `t ↦ p(t, x, y)` extends to a
  holomorphic function on `Re t > 0` and tends to `1`, so the identity theorem excludes it.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace HarmonicBalls

/-- The bump `y ↦ (r - |y - y₀|)⁺`. -/
noncomputable def bumpFunction (y₀ : ℂ) (r : ℝ) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun y => max 0 (r - ‖y - y₀‖),
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)⟩ (2 * |r|)
    fun y z => by
      have h : ∀ w : ℂ, |max 0 (r - ‖w - y₀‖)| ≤ |r| := fun w => by
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le (abs_nonneg _) ((sub_le_self _ (norm_nonneg _)).trans (le_abs_self _))
      show dist (max 0 (r - ‖y - y₀‖)) (max 0 (r - ‖z - y₀‖)) ≤ 2 * |r|
      rw [Real.dist_eq]
      linarith [abs_sub (max 0 (r - ‖y - y₀‖)) (max 0 (r - ‖z - y₀‖)), h y, h z]

theorem bumpFunction_apply (y₀ : ℂ) (r : ℝ) (y : ℂ) :
    bumpFunction y₀ r y = max 0 (r - ‖y - y₀‖) := rfl

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} [IsProbabilityMeasure (unitSquareRevuzMeasure A)]
  {hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A)} (E : GreenEigenData hν)

/-- **Nonnegativity of the kernel.** -/
theorem eigenKernel_nonneg (hA : IsUnitSquarePCAF A)
    (hsupp : ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r →
      0 < unitSquareRevuzMeasure A (ball y r ∩ closedSquare 0 1))
    {v : ℝ} (hv : 0 < v) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) {y₀ : ℂ}
    (hy₀ : y₀ ∈ closedSquare (0 : ℂ) 1) : 0 ≤ E.eigenKernel v x y₀ := by
  by_contra hneg
  have hneg' : E.eigenKernel v x y₀ < 0 := lt_of_not_ge hneg
  obtain ⟨r, hr, hrb⟩ := Metric.continuousWithinAt_iff.1
    ((E.continuousOn_eigenKernel_right hv hx) y₀ hy₀) (-E.eigenKernel v x y₀ / 2) (by linarith)
  have hsmall : ∀ y ∈ closedSquare (0 : ℂ) 1, ‖y - y₀‖ < r →
      E.eigenKernel v x y < E.eigenKernel v x y₀ / 2 := by
    intro y hy hyr
    have h := hrb hy (by rw [dist_eq_norm]; exact hyr)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  set ψ := bumpFunction y₀ r with hψ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => le_max_left _ _
  have hψm : Measurable ψ := ψ.continuous.measurable
  have hψb : ∀ y, |ψ y| ≤ ‖ψ‖ := fun y => by rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm y
  have hid := timeChangeTransition_eq_integral_eigenKernel E hA ψ hx hv
  have hT0 : 0 ≤ timeChangeTransition A ψ v x := integral_nonneg fun _ => hψ0 _
  have hpi : Integrable (fun y => E.eigenKernel v x y * ψ y) (unitSquareRevuzMeasure A) :=
    (E.integrable_eigenKernel_mul hv hx ψ.continuous.continuousOn hψb).2
  have hψi : Integrable ψ (unitSquareRevuzMeasure A) := integrable_of_abs_le hψm hψb
  -- the kernel side is negative
  have hle : ∫ y, E.eigenKernel v x y * ψ y ∂(unitSquareRevuzMeasure A) ≤
      (E.eigenKernel v x y₀ / 2) * ∫ y, ψ y ∂(unitSquareRevuzMeasure A) := by
    rw [← integral_const_mul]
    refine integral_mono_ae hpi (hψi.const_mul _) ?_
    filter_upwards [hν.ae_mem] with y hy
    by_cases hyr : ‖y - y₀‖ < r
    · exact mul_le_mul_of_nonneg_right (hsmall y hy hyr).le (hψ0 y)
    · have : ψ y = 0 := by
        rw [hψ, bumpFunction_apply]
        exact max_eq_left (by linarith [not_lt.1 hyr])
      rw [this, mul_zero, mul_zero]
  have hpos : 0 < ∫ y, ψ y ∂(unitSquareRevuzMeasure A) := by
    have hball := hsupp y₀ hy₀ (r / 2) (by positivity)
    have hlow : ∫ y, (ball y₀ (r / 2) ∩ closedSquare 0 1).indicator (fun _ => r / 2) y
        ∂(unitSquareRevuzMeasure A) ≤
        ∫ y, ψ y ∂(unitSquareRevuzMeasure A) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => indicator_nonneg
        (fun _ _ => by positivity) _) hψi (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ ball y₀ (r / 2) ∩ closedSquare 0 1
      · rw [indicator_of_mem hy, hψ, bumpFunction_apply]
        have : ‖y - y₀‖ < r / 2 := by rw [← dist_eq_norm]; exact hy.1
        exact le_max_of_le_right (by linarith)
      · rw [indicator_of_notMem hy]
        exact hψ0 y
    have hval : ∫ y, (ball y₀ (r / 2) ∩ closedSquare 0 1).indicator (fun _ => r / 2) y
        ∂(unitSquareRevuzMeasure A) =
        (r / 2) * ((unitSquareRevuzMeasure A) (ball y₀ (r / 2) ∩ closedSquare 0 1)).toReal := by
      rw [integral_indicator (measurableSet_ball.inter measurableSet_closedSquare_zero_one),
        setIntegral_const, smul_eq_mul, measureReal_def]
      ring
    have hmeas : 0 < ((unitSquareRevuzMeasure A) (ball y₀ (r / 2) ∩ closedSquare 0 1)).toReal :=
      ENNReal.toReal_pos hball.ne' (measure_ne_top _ _)
    rw [hval] at hlow
    nlinarith
  have : ∫ y, E.eigenKernel v x y * ψ y ∂(unitSquareRevuzMeasure A) < 0 := by nlinarith
  linarith

/-- **The law of the time change at time `v` from `x`** is `p(v, x, y) ν(dy)`. -/
theorem map_clockPair_eq_withDensity (hA : IsUnitSquarePCAF A)
    (hsupp : ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r →
      0 < unitSquareRevuzMeasure A (ball y r ∩ closedSquare 0 1))
    {v : ℝ} (hv : 0 < v) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    (reflectedPlanarBrownianMotion 0 1 x).map (fun b => (clockPair A (b, v)).2) =
      (unitSquareRevuzMeasure A).withDensity fun y => ENNReal.ofReal (E.eigenKernel v x y) := by
  have hYm : Measurable fun b => (clockPair A (b, v)).2 :=
    (measurable_clockPair hA.measurable).snd.comp (measurable_id.prodMk measurable_const)
  have hrestr : (unitSquareRevuzMeasure A).restrict (closedSquare 0 1) =
      unitSquareRevuzMeasure A := Measure.restrict_eq_self_of_ae_mem hν.ae_mem
  have hpm : AEMeasurable (fun y => E.eigenKernel v x y) (unitSquareRevuzMeasure A) := by
    have h := (E.continuousOn_eigenKernel_right hv hx).aemeasurable
      (μ := unitSquareRevuzMeasure A)
      measurableSet_closedSquare_zero_one
    rwa [hrestr] at h
  have hpint : Integrable (fun y => E.eigenKernel v x y) (unitSquareRevuzMeasure A) := by
    have h := (E.integrable_eigenKernel_mul hv hx (g := fun _ => 1) continuousOn_const
      (C := 1) fun _ => by simp).2
    simpa using h
  have : IsFiniteMeasure ((unitSquareRevuzMeasure A).withDensity
      fun y => ENNReal.ofReal (E.eigenKernel v x y)) :=
    isFiniteMeasure_withDensity_ofReal hpint.2
  have : IsFiniteMeasure ((reflectedPlanarBrownianMotion 0 1 x).map
      fun b => (clockPair A (b, v)).2) := Measure.isFiniteMeasure_map _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun ψ => ?_
  rw [integral_map hYm.aemeasurable ψ.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hpm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h := timeChangeTransition_eq_integral_eigenKernel E hA ψ hx hv
  unfold timeChangeTransition at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hν.ae_mem] with y hy
  rw [ENNReal.toReal_ofReal (eigenKernel_nonneg E hA hsupp hv hx hy), smul_eq_mul]

/-- **The eigenfunction kernel is a heat kernel of the time change** from every start of `K₀`. -/
theorem isLBMHeatKernel_eigenKernel (hA : IsUnitSquarePCAF A)
    (hsupp : ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r →
      0 < unitSquareRevuzMeasure A (ball y r ∩ closedSquare 0 1)) :
    IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) (unitSquareRevuzMeasure A) E.eigenKernel := by
  intro t ht x hx
  refine ⟨fun y hy => eigenKernel_nonneg E hA hsupp ht hx hy, fun S hS => ?_⟩
  have hYm : Measurable fun b => (clockPair A (b, t)).2 :=
    (measurable_clockPair hA.measurable).snd.comp (measurable_id.prodMk measurable_const)
  have e1 : {b : ContinuousPath ℂ |
      liouvilleBrownianPath (fun b t => (A t b : ℝ)) b t.toNNReal ∈ S} =
      {b | b (pcafClockInverse A t.toNNReal b) ∈ S} := by
    ext b
    simp only [mem_ofPred_eq, liouvilleBrownianPath_coe_eq]
  rw [e1, reflected_eval_pcafClockInverse_mem hA hx]
  have h := congrArg (fun m : Measure ℂ => m S) (map_clockPair_eq_withDensity E hA hsupp ht hx)
  simp only [Measure.map_apply hYm hS, withDensity_apply _ hS] at h
  rw [show unitSquareTimeChangeRegularized A t.toNNReal ⁻¹' S =
    (fun b => (clockPair A (b, t)).2) ⁻¹' S from rfl, h]
  have hSK : S =ᵐ[unitSquareRevuzMeasure A] (S ∩ closedSquare 0 1 : Set ℂ) := by
    filter_upwards [hν.ae_mem] with y hy
    simp [hy]
  rw [Measure.restrict_congr_set hSK]

/-- `p(s, y, y) ≥ 1`. -/
theorem one_le_eigenKernel_self {s : ℝ} (y : ℂ) : 1 ≤ E.eigenKernel s y y := by
  unfold GreenEigenData.eigenKernel
  have : 0 ≤ ∑' i, Real.exp (-(s / E.eig i)) * (E.eigenfun i y * E.eigenfun i y) :=
    tsum_nonneg fun i => mul_nonneg (Real.exp_pos _).le (mul_self_nonneg (E.eigenfun i y))
  linarith

/-- The integral over `K₀` of a nonnegative function continuous on `K₀` and positive at a point is
positive. -/
theorem setIntegral_pos_of_continuousOn (hsupp : ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r →
      0 < unitSquareRevuzMeasure A (ball y r ∩ closedSquare 0 1))
    {g : ℂ → ℝ} (hg : ContinuousOn g (closedSquare 0 1))
    (hg0 : ∀ y ∈ closedSquare (0 : ℂ) 1, 0 ≤ g y)
    (hint : IntegrableOn g (closedSquare 0 1) (unitSquareRevuzMeasure A)) {y₀ : ℂ}
    (hy₀ : y₀ ∈ closedSquare (0 : ℂ) 1) (hpos : 0 < g y₀) :
    0 < ∫ y in closedSquare 0 1, g y ∂unitSquareRevuzMeasure A := by
  obtain ⟨r, hr, hrb⟩ := Metric.continuousWithinAt_iff.1 (hg y₀ hy₀) (g y₀ / 2) (by linarith)
  have hball := hsupp y₀ hy₀ r hr
  have hlow : ∫ y in closedSquare 0 1, (ball y₀ r ∩ closedSquare 0 1).indicator
      (fun _ => g y₀ / 2) y ∂(unitSquareRevuzMeasure A) ≤
        ∫ y in closedSquare 0 1, g y ∂(unitSquareRevuzMeasure A) := by
    refine setIntegral_mono_on ?_ hint measurableSet_closedSquare_zero_one fun y hy => ?_
    · exact (integrable_const (g y₀ / 2)).indicator
        (measurableSet_ball.inter measurableSet_closedSquare_zero_one) |>.integrableOn
    · by_cases hyb : y ∈ ball y₀ r ∩ closedSquare 0 1
      · rw [indicator_of_mem hyb]
        have h := hrb hy (by rw [← mem_ball]; exact hyb.1)
        rw [Real.dist_eq, abs_lt] at h
        linarith [h.1]
      · rw [indicator_of_notMem hyb]
        exact hg0 y hy
  have hval : ∫ y in closedSquare 0 1, (ball y₀ r ∩ closedSquare 0 1).indicator
      (fun _ => g y₀ / 2) y ∂(unitSquareRevuzMeasure A) =
        (g y₀ / 2) * ((unitSquareRevuzMeasure A) (ball y₀ r ∩ closedSquare 0 1)).toReal := by
    rw [integral_indicator (measurableSet_ball.inter measurableSet_closedSquare_zero_one),
      Measure.restrict_restrict (measurableSet_ball.inter measurableSet_closedSquare_zero_one),
      inter_assoc, inter_self, setIntegral_const, smul_eq_mul, measureReal_def]
    ring
  have hmeas : 0 < ((unitSquareRevuzMeasure A) (ball y₀ r ∩ closedSquare 0 1)).toReal :=
    ENNReal.toReal_pos hball.ne' (measure_ne_top _ _)
  rw [hval] at hlow
  nlinarith

theorem eigenKernel_comm (s : ℝ) (z y : ℂ) : E.eigenKernel s z y = E.eigenKernel s y z := by
  unfold GreenEigenData.eigenKernel
  congr 1
  exact tsum_congr fun i => by ring

/-- **Strict positivity of the kernel** on `(0, ∞) × K₀ × K₀`. -/
theorem eigenKernel_pos (hA : IsUnitSquarePCAF A)
    (hsupp : ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r →
      0 < unitSquareRevuzMeasure A (ball y r ∩ closedSquare 0 1))
    {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) {y : ℂ}
    (hy : y ∈ closedSquare (0 : ℂ) 1) : 0 < E.eigenKernel t x y := by
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  have hp := isLBMHeatKernel_eigenKernel E hA hsupp
  have hpc := E.continuousOn_eigenKernel
  have hatom : ∀ z ∈ closedSquare (0 : ℂ) 1, (unitSquareRevuzMeasure A) {z} = 0 :=
    fun z hz => hν.singleton_eq_zero hz
  set D := 24 * B ^ 2 * (∑' i, E.eig i ^ 2) with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (by positivity) (tsum_nonneg fun i => sq_nonneg _)
  have hpb : ∀ {u : ℝ}, 0 < u → ∀ z w, |E.eigenKernel u z w| ≤ 1 + D / u ^ 4 := by
    intro u hu z w
    have h := E.abs_eigenKernel_sub_one_le hB0 hB hu z w
    rw [← hD, abs_le] at h
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  -- a positive value stays positive
  have hfwd : ∀ {u : ℝ}, 0 < u → 0 < E.eigenKernel u x y → ∀ {s : ℝ}, 0 < s →
      0 < E.eigenKernel (u + s) x y := by
    intro u hu hpos s hs
    rw [IsLBMHeatKernel.chapmanKolmogorov hA hsupp hatom hp hpc hu hs hx hy]
    have hcs : ContinuousOn (fun z => E.eigenKernel s z y) (closedSquare 0 1) :=
      (E.continuousOn_eigenKernel_right hs hy).congr fun z _ => eigenKernel_comm E s z y
    have hgc : ContinuousOn (fun z => E.eigenKernel u x z * E.eigenKernel s z y)
        (closedSquare 0 1) := (E.continuousOn_eigenKernel_right hu hx).mul hcs
    have hint : IntegrableOn (fun z => E.eigenKernel u x z * E.eigenKernel s z y)
        (closedSquare 0 1) (unitSquareRevuzMeasure A) := by
      refine Integrable.of_bound (hgc.aestronglyMeasurable measurableSet_closedSquare_zero_one)
        ((1 + D / u ^ 4) * (1 + D / s ^ 4)) (Eventually.of_forall fun z => ?_)
      show ‖E.eigenKernel u x z * E.eigenKernel s z y‖ ≤ (1 + D / u ^ 4) * (1 + D / s ^ 4)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hpb hu x z) (hpb hs z y) (abs_nonneg _)
        ((abs_nonneg _).trans (hpb hu x z))
    refine setIntegral_pos_of_continuousOn hsupp hgc (fun z hz => mul_nonneg
      (eigenKernel_nonneg E hA hsupp hu hx hz) (eigenKernel_nonneg E hA hsupp hs hz hy)) hint hy ?_
    exact mul_pos hpos (lt_of_lt_of_le one_pos (one_le_eigenKernel_self E y))
  by_contra hneg
  have h0 : E.eigenKernel t x y = 0 :=
    le_antisymm (not_lt.1 hneg) (eigenKernel_nonneg E hA hsupp ht hx hy)
  -- the kernel vanishes before `t`
  have hbefore : ∀ u ∈ Ioo (0 : ℝ) t, E.eigenKernel u x y = 0 := by
    intro u hu
    by_contra hne
    have hpos : 0 < E.eigenKernel u x y :=
      lt_of_le_of_ne (eigenKernel_nonneg E hA hsupp hu.1 hx hy) (Ne.symm hne)
    have h := hfwd hu.1 hpos (s := t - u) (by linarith [hu.2])
    rw [show u + (t - u) = t by ring, h0] at h
    exact lt_irrefl _ h
  -- the holomorphic extension in time
  set F : ℂ → ℂ := fun z => 1 + ∑' i, Complex.exp (-(z / E.eig i)) *
    ((E.eigenfun i x * E.eigenfun i y : ℝ) : ℂ) with hF
  have hFreal : ∀ s : ℝ, F s = (E.eigenKernel s x y : ℂ) := by
    intro s
    rw [hF]
    simp only [GreenEigenData.eigenKernel]
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_tsum]
    congr 1
    refine tsum_congr fun i => ?_
    push_cast
    ring_nf
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz' : 0 < z.re := hz
    have hε0 : 0 < z.re / 2 := by positivity
    have hUε : IsOpen {w : ℂ | z.re / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hsumm : Summable fun i => 24 * B ^ 2 * E.eig i ^ 2 / (z.re / 2) ^ 4 :=
      ((E.summable_eig_sq hB0 hB).1.mul_left (24 * B ^ 2)).div_const ((z.re / 2) ^ 4)
    have hd : DifferentiableOn ℂ (fun w => ∑' i, Complex.exp (-(w / E.eig i)) *
        ((E.eigenfun i x * E.eigenfun i y : ℝ) : ℂ)) {w : ℂ | z.re / 2 < w.re} := by
      refine Complex.differentiableOn_tsum_of_summable_norm hsumm (fun i => ?_) hUε fun i w hw => ?_
      · exact ((differentiable_id.div_const _).neg.cexp.mul_const _).differentiableOn
      · have hw' : z.re / 2 < w.re := hw
        have hμ := E.eig_pos i
        have hterm := E.abs_term_le hB0 hB i hε0 x y
        rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
        have hre : (-(w / (E.eig i : ℂ))).re = -(w.re / E.eig i) := by
          rw [Complex.neg_re, Complex.div_ofReal_re]
        rw [hre]
        refine le_trans ?_ hterm
        rw [abs_mul (Real.exp _), abs_of_pos (Real.exp_pos _), abs_mul (E.eigenfun i x)]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
        have := (div_lt_div_iff_of_pos_right hμ).2 hw'
        linarith
    have hmem : z ∈ {w : ℂ | z.re / 2 < w.re} := by
      show z.re / 2 < z.re
      linarith
    exact (((differentiableOn_const (1 : ℂ)).add hd).differentiableAt
      (hUε.mem_nhds hmem)).differentiableWithinAt
  have han := hdiff.analyticOnNhd hU
  have hpre : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hz₀U : ((t / 2 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    show 0 < (((t / 2 : ℝ) : ℂ)).re
    rw [Complex.ofReal_re]
    positivity
  have hzs_mem : ∀ n : ℕ, t / 2 + t / 4 * (1 / ((n : ℝ) + 1)) ∈ Ioo (0 : ℝ) t := fun n => by
    have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    constructor <;> nlinarith
  have hzs_ne : ∀ n : ℕ, (((t / 2 + t / 4 * (1 / ((n : ℝ) + 1)) : ℝ)) : ℂ) ≠ ((t / 2 : ℝ) : ℂ) := by
    intro n h
    have h' : t / 2 + t / 4 * (1 / ((n : ℝ) + 1)) = t / 2 := Complex.ofReal_injective h
    have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    nlinarith
  have hzs_lim : Tendsto (fun n : ℕ => (((t / 2 + t / 4 * (1 / ((n : ℝ) + 1)) : ℝ)) : ℂ)) atTop
      (𝓝[≠] ((t / 2 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hzs_ne⟩
    have h1 : Tendsto (fun n : ℕ => t / 2 + t / 4 * (1 / ((n : ℝ) + 1))) atTop (𝓝 (t / 2)) := by
      have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (t / 4)
      have h3 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => t / 2) atTop (𝓝 (t / 2))).add h2
      rwa [mul_zero, add_zero] at h3
    exact (Complex.continuous_ofReal.tendsto _).comp h1
  have hfreq : ∃ᶠ z in 𝓝[≠] ((t / 2 : ℝ) : ℂ), F z = 0 := by
    refine hzs_lim.frequently (Frequently.of_forall fun n => ?_)
    rw [hFreal, hbefore _ (hzs_mem n), Complex.ofReal_zero]
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hz₀U hfreq
  -- but the kernel tends to `1`
  set s : ℝ := max 1 (2 * D + 2) with hs
  have hs1 : 1 ≤ s := le_max_left _ _
  have hs0 : 0 < s := by linarith
  have hsU : ((s : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    show 0 < (((s : ℝ) : ℂ)).re
    rw [Complex.ofReal_re]
    exact hs0
  have hFs := hzero hsU
  rw [hFreal, Pi.zero_apply, Complex.ofReal_eq_zero] at hFs
  have hclose := E.abs_eigenKernel_sub_one_le hB0 hB hs0 x y
  rw [← hD] at hclose
  have hs4 : s ≤ s ^ 4 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hD' : D / s ^ 4 < 1 := by
    rw [div_lt_one (pow_pos hs0 4)]
    have : 2 * D + 2 ≤ s := le_max_right _ _
    linarith
  rw [hFs, zero_sub, abs_neg, abs_one] at hclose
  linarith

end HarmonicBalls

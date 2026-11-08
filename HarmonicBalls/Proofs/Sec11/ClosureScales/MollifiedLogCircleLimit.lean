import Mathlib
import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Sec11.ClosureScales.CirclePotential
import HarmonicBalls.Proofs.Sec11.ClosureScales.RootedShiftProfile
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-!
# Deterministic logarithmic-insertion limit of mollified circle averages

Source: r10 `l:r9-circle-code`, lines 1331-1350 (Fubini plus the circle-potential formula).

Let `rho` be continuous on `ℂ` with `tsupport rho ⊆ closedBall 0 1` and `∫ rho = 1`, and let
`rho_e(x) = e⁻² rho(e⁻¹ • x)` for `e > 0`. For `r > 0`, `w z : ℂ` and `γ : ℝ`, the integrand
`v ↦ dmsShift γ z v * circleAverage (fun u ↦ rho_e (u - v)) w r` is integrable for every `e > 0`, and as
`e → 0⁺` its integral tends to `-γ * log (max r ‖w - z‖) + γ * circleAverage logMaxOne w r`, for every `z`
(including `z` on the circle).

Route. Writing the circle average as an integral over `θ ∈ (0, 2π]` and applying Fubini twice, with the
change of variables `v = circleMap - y`, the integral equals `∫ rho_e(y) * circleAverage (fun u ↦ g (u - y)) w r dy`.
For `g = log ‖· - z‖` the inner average is the logarithmic potential `log max(r, ‖(y + z) - w‖)` of the uniform
circle measure (Armitage-Gardiner potential theory), and for `g = logMaxOne` it is continuous in the centre.
Both limits are the approximate identity at `y = 0`. No Gaussian event, decoder or literature hypothesis is used.
`dmsShift` is the Proposed definition in `HarmonicBalls.Proposed.DuplantierMillerSheffield`; this file uses its
formula only (source review of that definition remains with the operator). The hypotheses `_h_even` and the
smoothness assumption are carried to match the statement; the limit uses only continuity and the support condition.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace HarmonicBalls

/-- The mollifier `e⁻² rho(e⁻¹ • x)` at scale `e`, with the literal formula of the statement. -/
def mollifierAt (rho : ℂ → ℝ) (e : ℝ) (x : ℂ) : ℝ :=
  ((e : ℝ) ^ 2)⁻¹ * rho ((e : ℝ)⁻¹ • x)

section Mollifier

variable {rho : ℂ → ℝ}

lemma rho_eq_zero_of_one_lt (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) {x : ℂ} (hx : 1 < ‖x‖) :
    rho x = 0 := by
  by_contra h
  have h1 : x ∈ tsupport rho := subset_tsupport rho (Function.mem_support.2 h)
  have h2 := h_supp h1
  rw [mem_closedBall, dist_zero_right] at h2
  linarith

lemma mollifierAt_eq_zero (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) {e : ℝ} (he : 0 < e) {x : ℂ}
    (hx : e < ‖x‖) : mollifierAt rho e x = 0 := by
  have h1 : 1 < ‖(e : ℝ)⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos he, inv_mul_eq_div, one_lt_div he]
    exact hx
  unfold mollifierAt
  rw [rho_eq_zero_of_one_lt h_supp h1, mul_zero]

lemma mollifierAt_nonneg (h0 : ∀ x, 0 ≤ rho x) (e : ℝ) (x : ℂ) : 0 ≤ mollifierAt rho e x := by
  unfold mollifierAt
  exact mul_nonneg (by positivity) (h0 _)

lemma mollifierAt_continuous (hc : Continuous rho) (e : ℝ) : Continuous (mollifierAt rho e) := by
  unfold mollifierAt
  exact continuous_const.mul (hc.comp (continuous_const_smul _))

lemma mollifierAt_zero_outside (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) {e : ℝ} (he : 0 < e) :
    ∀ x, x ∉ closedBall (0 : ℂ) e → mollifierAt rho e x = 0 := fun x hx =>
  mollifierAt_eq_zero h_supp he (by simpa [mem_closedBall, dist_zero_right] using hx)

lemma mollifierAt_hasCompactSupport (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) {e : ℝ} (he : 0 < e) :
    HasCompactSupport (mollifierAt rho e) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) e) (mollifierAt_zero_outside h_supp he)

/-- The mollifier has total mass one: the change of variables `x ↦ e⁻¹ • x` on `ℂ` (real dimension two). -/
lemma mollifierAt_integral (hint : ∫ x : ℂ, rho x = 1) {e : ℝ} (he : 0 < e) :
    ∫ x : ℂ, mollifierAt rho e x = 1 := by
  unfold mollifierAt
  rw [integral_const_mul, Measure.integral_comp_smul, hint, Complex.finrank_real_complex, smul_eq_mul,
    mul_one]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((e : ℝ)⁻¹ ^ 2)⁻¹)]
  field_simp

/-- Approximate identity at `0`: `∫ rho_e * h → h 0` as `e → 0⁺`, for continuous `h`. -/
lemma tendsto_integral_mollifierAt_mul (hc : Continuous rho) (h0 : ∀ x, 0 ≤ rho x)
    (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) (hint : ∫ x : ℂ, rho x = 1)
    {h : ℂ → ℝ} (hh : Continuous h) :
    Tendsto (fun e : ℝ => ∫ y : ℂ, mollifierAt rho e y * h y) (𝓝[>] 0) (𝓝 (h 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuous_iff.1 hh 0 (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {e} he hed => ?_⟩
  have he0 : 0 < e := he
  rw [Real.dist_eq, sub_zero, abs_of_pos he0] at hed
  have hI : Integrable (fun y : ℂ => mollifierAt rho e y) :=
    (mollifierAt_continuous hc e).integrable_of_hasCompactSupport
      (mollifierAt_hasCompactSupport h_supp he0)
  have hIh : Integrable (fun y : ℂ => mollifierAt rho e y * h y) :=
    ((mollifierAt_continuous hc e).mul hh).integrable_of_hasCompactSupport
      ((mollifierAt_hasCompactSupport h_supp he0).mul_right)
  have hdiff : (∫ y : ℂ, mollifierAt rho e y * h y) - h 0
      = ∫ y : ℂ, mollifierAt rho e y * (h y - h 0) := by
    have h1 : ∫ y : ℂ, mollifierAt rho e y * h 0 = h 0 := by
      rw [integral_mul_const, mollifierAt_integral hint he0, one_mul]
    calc (∫ y : ℂ, mollifierAt rho e y * h y) - h 0
        = (∫ y : ℂ, mollifierAt rho e y * h y) - ∫ y : ℂ, mollifierAt rho e y * h 0 := by rw [h1]
      _ = ∫ y : ℂ, (mollifierAt rho e y * h y - mollifierAt rho e y * h 0) :=
          (integral_sub hIh (hI.mul_const (h 0))).symm
      _ = ∫ y : ℂ, mollifierAt rho e y * (h y - h 0) := by
          congr 1
          funext y
          ring
  have hpt : ∀ y : ℂ, ‖mollifierAt rho e y * (h y - h 0)‖ ≤ mollifierAt rho e y * (ε / 2) := by
    intro y
    have hnn := mollifierAt_nonneg h0 e y
    by_cases hy : e < ‖y‖
    · simp [mollifierAt_eq_zero h_supp he0 hy]
    · rw [not_lt] at hy
      have hdist : dist y 0 < δ := by
        rw [dist_zero_right]
        linarith
      have hhy : |h y - h 0| < ε / 2 := by
        have := hδh y hdist
        rwa [Real.dist_eq] at this
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left hhy.le hnn
  have hbound : ‖∫ y : ℂ, mollifierAt rho e y * (h y - h 0)‖ ≤ ε / 2 := by
    have key := norm_integral_le_of_norm_le (hI.mul_const (ε / 2)) (ae_of_all _ hpt)
    rw [integral_mul_const, mollifierAt_integral hint he0, one_mul] at key
    exact key
  rw [Real.dist_eq, hdiff]
  rw [Real.norm_eq_abs] at hbound
  linarith

/-- The circle average as an integral over `θ ∈ (0, 2π]`. -/
lemma circleAverage_eq_integral (f : ℂ → ℝ) (w : ℂ) (r : ℝ) :
    Real.circleAverage f w r = (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), f (circleMap w r θ) := by
  unfold Real.circleAverage
  rw [intervalIntegral.integral_of_le (by positivity), smul_eq_mul]

/-- Translating the integration variable of a circle average moves the centre. -/
lemma circleAverage_comp_sub (f : ℂ → ℝ) (w y : ℂ) (r : ℝ) :
    Real.circleAverage (fun u => f (u - y)) w r = Real.circleAverage f (w - y) r := by
  have key : ∀ θ : ℝ, circleMap w r θ - y = circleMap (w - y) r θ := fun θ => by
    simp only [circleMap]
    ring
  unfold Real.circleAverage
  simp only [key]

/-- The logarithmic potential of the uniform circle measure, at the point `y + z`. -/
lemma circleAverage_log_sub (y z w : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun u : ℂ => Real.log ‖u - y - z‖) w r = Real.log (max r ‖(y + z) - w‖) := by
  have hfun : (fun u : ℂ => Real.log ‖u - y - z‖) = fun u : ℂ => Real.log ‖u - (y + z)‖ := by
    funext u
    rw [sub_sub]
  rw [hfun]
  exact HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max hr

lemma continuous_log_max_sub (w z : ℂ) {r : ℝ} (hr : 0 < r) :
    Continuous fun y : ℂ => Real.log (max r ‖(y + z) - w‖) := by
  have hc : Continuous fun y : ℂ => max r ‖(y + z) - w‖ := by fun_prop
  exact hc.log fun y => (lt_max_of_lt_left hr).ne'

lemma continuous_circleAverage_logMaxOne_sub (w : ℂ) (r : ℝ) :
    Continuous fun y : ℂ => Real.circleAverage logMaxOne (w - y) r :=
  continuous_circleAverage_logMaxOne.comp
    ((continuous_const.sub continuous_id).prodMk continuous_const)

/-- The mollified circle average is continuous in the base point. -/
lemma continuous_circleAverage_mollifierAt (hc : Continuous rho) (w : ℂ) (r e : ℝ) :
    Continuous fun v : ℂ => Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r := by
  have hu : Continuous fun q : ℂ × ℝ => mollifierAt rho e (circleMap w r q.2 - q.1) := by
    refine (mollifierAt_continuous hc e).comp ?_
    unfold circleMap
    fun_prop
  have hI : Continuous fun v : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), mollifierAt rho e (circleMap w r θ - v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (v : ℂ) (θ : ℝ) => mollifierAt rho e (circleMap w r θ - v)) hu 0 (2 * Real.pi)
  unfold Real.circleAverage
  simp only [smul_eq_mul]
  exact continuous_const.mul hI

lemma mollifierAt_circle_eq_zero_of_far (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) (w : ℂ) {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) {v : ℂ} (hv : v ∉ closedBall w (r + e)) (θ : ℝ) :
    mollifierAt rho e (circleMap w r θ - v) = 0 := by
  apply mollifierAt_eq_zero h_supp he
  have hv' : r + e < ‖v - w‖ := by
    rw [mem_closedBall, not_le, dist_eq_norm] at hv
    exact hv
  have hcw : ‖circleMap w r θ - w‖ = r := by
    simp only [circleMap, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
  have htri : ‖v - w‖ ≤ ‖v - circleMap w r θ‖ + ‖circleMap w r θ - w‖ := by
    have := norm_add_le (v - circleMap w r θ) (circleMap w r θ - w)
    rwa [sub_add_sub_cancel] at this
  rw [norm_sub_rev]
  linarith

lemma circleAverage_mollifierAt_eq_zero (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) (w : ℂ) {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) {v : ℂ} (hv : v ∉ closedBall w (r + e)) :
    Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r = 0 := by
  rw [circleAverage_eq_integral]
  simp [mollifierAt_circle_eq_zero_of_far h_supp w hr he hv]

lemma exists_norm_bound_of_zero_outside {f : ℂ → ℝ} (hf : Continuous f) {c : ℂ} {R : ℝ}
    (hz : ∀ x, x ∉ closedBall c R → f x = 0) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C0 0, fun x => ?_⟩
  by_cases hx : x ∈ closedBall c R
  · exact (hC0 x hx).trans (le_max_left _ _)
  · rw [hz x hx, norm_zero]
    exact le_max_right _ _

/-- A locally integrable function times a continuous function vanishing off a ball is integrable. -/
lemma integrable_mul_of_zero_outside {g φ : ℂ → ℝ} (hgl : LocallyIntegrable g) (hgm : Measurable g)
    (hφ : Continuous φ) {c : ℂ} {R : ℝ} (hz : ∀ x, x ∉ closedBall c R → φ x = 0) :
    Integrable (fun x => g x * φ x) := by
  obtain ⟨C, hC⟩ := exists_norm_bound_of_zero_outside hφ hz
  have h1 : IntegrableOn (fun x => C * ‖g x‖) (closedBall c R) :=
    (Integrable.norm (hgl.integrableOn_isCompact (isCompact_closedBall c R))).const_mul C
  refine Integrable.mono' (h1.integrable_indicator measurableSet_closedBall)
    (hgm.mul hφ.measurable).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ closedBall c R
  · simp only [Set.indicator_of_mem hx, norm_mul]
    calc ‖g x‖ * ‖φ x‖ ≤ ‖g x‖ * C := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
      _ = C * ‖g x‖ := mul_comm _ _
  · simp [Set.indicator_of_notMem hx, hz x hx]

/-- Integrability on a product from a uniform bound on the inner integrals. -/
lemma integrable_prod_of_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α × β → ℝ} (hf : Measurable f)
    {G : α → ℝ} (hG : Integrable G μ) (hfb : ∀ a, Integrable (fun b => f (a, b)) ν)
    (hbd : ∀ a, ∫ b, ‖f (a, b)‖ ∂ν ≤ G a) : Integrable f (μ.prod ν) := by
  rw [integrable_prod_iff hf.aestronglyMeasurable]
  refine ⟨ae_of_all _ hfb, Integrable.mono' hG ?_ (ae_of_all _ fun a => ?_)⟩
  · exact hf.norm.aestronglyMeasurable.integral_prod_right'
  · rw [Real.norm_of_nonneg (integral_nonneg fun b => norm_nonneg _)]
    exact hbd a

/-- The pointwise domination of the circle-mollified integrand, uniformly in the angle `θ`. -/
lemma norm_mul_mollifierAt_circle_le (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) (w : ℂ) {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) {K0 : ℝ} (hK0 : ∀ x, ‖mollifierAt rho e x‖ ≤ K0) (g : ℂ → ℝ)
    (θ : ℝ) (v : ℂ) :
    ‖g v * mollifierAt rho e (circleMap w r θ - v)‖ ≤
      Set.indicator (closedBall w (r + e)) (fun v : ℂ => K0 * ‖g v‖) v := by
  by_cases hv : v ∈ closedBall w (r + e)
  · rw [Set.indicator_of_mem hv, norm_mul]
    calc ‖g v‖ * ‖mollifierAt rho e (circleMap w r θ - v)‖ ≤ ‖g v‖ * K0 :=
          mul_le_mul_of_nonneg_left (hK0 _) (norm_nonneg _)
      _ = K0 * ‖g v‖ := mul_comm _ _
  · simp [Set.indicator_of_notMem hv, mollifierAt_circle_eq_zero_of_far h_supp w hr he hv θ]

/-- Fubini on the circle: the mollified integral of `g` equals the mollified circle averages of `g`. -/
theorem integral_mul_circleAverage_mollifierAt (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1)
    (hc : Continuous rho) {g : ℂ → ℝ} (hgm : Measurable g) (hgl : LocallyIntegrable g) (w : ℂ) {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) :
    ∫ v : ℂ, g v * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r =
      ∫ y : ℂ, mollifierAt rho e y * Real.circleAverage (fun u : ℂ => g (u - y)) w r := by
  obtain ⟨K0, hK0⟩ := exists_norm_bound_of_zero_outside (mollifierAt_continuous hc e)
    (mollifierAt_zero_outside h_supp he)
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hB : Integrable (Set.indicator (closedBall w (r + e)) (fun v : ℂ => K0 * ‖g v‖)) := by
    have h1 : IntegrableOn (fun v : ℂ => K0 * ‖g v‖) (closedBall w (r + e)) :=
      (Integrable.norm (hgl.integrableOn_isCompact (isCompact_closedBall w (r + e)))).const_mul K0
    exact h1.integrable_indicator measurableSet_closedBall
  have hcm : Continuous fun p : ℂ × ℝ => circleMap w r p.2 - p.1 := by
    unfold circleMap
    fun_prop
  have hcm' : Continuous fun p : ℝ × ℂ => circleMap w r p.1 - p.2 := by
    unfold circleMap
    fun_prop
  have hFm : Measurable fun p : ℂ × ℝ => g p.1 * mollifierAt rho e (circleMap w r p.2 - p.1) :=
    (hgm.comp measurable_fst).mul ((mollifierAt_continuous hc e).comp hcm).measurable
  have hKm : Measurable fun p : ℝ × ℂ => g (circleMap w r p.1 - p.2) * mollifierAt rho e p.2 :=
    (hgm.comp hcm'.measurable).mul ((mollifierAt_continuous hc e).measurable.comp measurable_snd)
  have hθc : ∀ v : ℂ, Continuous fun θ : ℝ => g v * mollifierAt rho e (circleMap w r θ - v) := by
    intro v
    refine continuous_const.mul ((mollifierAt_continuous hc e).comp ?_)
    unfold circleMap
    fun_prop
  have hvc : ∀ θ : ℝ, Continuous fun v : ℂ => circleMap w r θ - v := by
    intro θ
    unfold circleMap
    fun_prop
  have hvm : ∀ θ : ℝ, Measurable fun v : ℂ => g v * mollifierAt rho e (circleMap w r θ - v) :=
    fun θ => hgm.mul ((mollifierAt_continuous hc e).comp (hvc θ)).measurable
  have hFint : ∀ θ : ℝ, Integrable (fun v : ℂ => g v * mollifierAt rho e (circleMap w r θ - v)) := by
    intro θ
    refine Integrable.mono' hB (hvm θ).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    exact norm_mul_mollifierAt_circle_le h_supp w hr he hK0 g θ v
  -- first Fubini: exchange the circle parameter and the integration variable
  have hR1 : Integrable (fun p : ℂ × ℝ => g p.1 * mollifierAt rho e (circleMap w r p.2 - p.1))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    refine integrable_prod_of_bound hFm
      (G := fun v : ℂ => (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real Set.univ *
        Set.indicator (closedBall w (r + e)) (fun v : ℂ => K0 * ‖g v‖) v)
      (hB.const_mul _) (fun v => (hθc v).integrableOn_Ioc) ?_
    intro v
    calc ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ‖g v * mollifierAt rho e (circleMap w r θ - v)‖
        ≤ ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
            Set.indicator (closedBall w (r + e)) (fun v : ℂ => K0 * ‖g v‖) v :=
          integral_mono ((hθc v).norm.integrableOn_Ioc) (integrable_const _)
            (fun θ => norm_mul_mollifierAt_circle_le h_supp w hr he hK0 g θ v)
      _ = (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).real Set.univ *
            Set.indicator (closedBall w (r + e)) (fun v : ℂ => K0 * ‖g v‖) v := by
          rw [integral_const, smul_eq_mul]
  -- second Fubini: exchange the angle and the variable `y = circleMap - v`
  have hR2 : Integrable (fun p : ℝ × ℂ => g (circleMap w r p.1 - p.2) * mollifierAt rho e p.2)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod volume) := by
    refine integrable_prod_of_bound hKm
      (G := fun _ : ℝ => ∫ v : ℂ, Set.indicator (closedBall w (r + e)) (fun v : ℂ => K0 * ‖g v‖) v)
      (integrable_const _) ?_ ?_
    · intro θ
      have hcomp := (hFint θ).comp_sub_left (circleMap w r θ)
      refine hcomp.congr (ae_of_all _ fun y => ?_)
      simp only [sub_sub_cancel]
    · intro θ
      have hsub := integral_sub_left_eq_self (μ := volume)
        (fun v : ℂ => ‖g v * mollifierAt rho e (circleMap w r θ - v)‖) (circleMap w r θ)
      simp only [sub_sub_cancel] at hsub
      show ∫ y : ℂ, ‖g (circleMap w r θ - y) * mollifierAt rho e y‖ ≤
        ∫ v : ℂ, Set.indicator (closedBall w (r + e)) (fun v : ℂ => K0 * ‖g v‖) v
      rw [hsub]
      exact integral_mono (hFint θ).norm hB (fun v => norm_mul_mollifierAt_circle_le h_supp w hr he hK0 g θ v)
  have hstep : ∀ θ : ℝ, ∫ v : ℂ, g v * mollifierAt rho e (circleMap w r θ - v)
      = ∫ y : ℂ, g (circleMap w r θ - y) * mollifierAt rho e y := by
    intro θ
    have hs := integral_sub_left_eq_self (μ := volume)
      (fun v : ℂ => g v * mollifierAt rho e (circleMap w r θ - v)) (circleMap w r θ)
    simp only [sub_sub_cancel] at hs
    exact hs.symm
  have hL : ∫ v : ℂ, g v * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r
      = (2 * Real.pi)⁻¹ * ∫ v : ℂ, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
          g v * mollifierAt rho e (circleMap w r θ - v) := by
    rw [← integral_const_mul]
    congr 1
    funext v
    simp only [circleAverage_eq_integral]
    rw [integral_const_mul]
    ring
  have hRHS : ∫ y : ℂ, mollifierAt rho e y * Real.circleAverage (fun u : ℂ => g (u - y)) w r
      = (2 * Real.pi)⁻¹ * ∫ y : ℂ, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
          g (circleMap w r θ - y) * mollifierAt rho e y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [circleAverage_eq_integral]
    rw [integral_mul_const]
    ring
  rw [hL, hRHS]
  congr 1
  rw [integral_integral_swap (f := fun (v : ℂ) (θ : ℝ) => g v * mollifierAt rho e (circleMap w r θ - v)) hR1]
  simp_rw [hstep]
  exact integral_integral_swap (f := fun (θ : ℝ) (y : ℂ) => g (circleMap w r θ - y) * mollifierAt rho e y) hR2

end Mollifier

/-- **Deterministic logarithmic-insertion limit** (r10 `l:r9-circle-code`, lines 1331-1350).

For `rho` even, nonnegative, smooth, with `tsupport rho ⊆ closedBall 0 1` and `∫ rho = 1`, and for `r > 0`,
`γ : ℝ`, `z w : ℂ`: the integrand `v ↦ dmsShift γ z v * circleAverage (fun u ↦ e⁻² rho(e⁻¹ • (u - v))) w r`
is integrable for every `e > 0`, and its integral tends to
`-γ * log (max r ‖w - z‖) + γ * circleAverage logMaxOne w r` as `e → 0⁺` through positive reals, for every `z`.
The support hypothesis is taken as `closedBall 0 1` (the weaker reading of "support in `B_1`"), so the statement
covers both the open and the closed unit ball. -/
theorem mollified_log_circle_limit
    (rho : ℂ → ℝ) (_h_even : ∀ x : ℂ, rho (-x) = rho x) (h_nonneg : ∀ x : ℂ, 0 ≤ rho x)
    (h_smooth : ContDiff ℝ ∞ rho) (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1)
    (h_one : ∫ x : ℂ, rho x = 1) (γ : ℝ) (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    (∀ e : ℝ, 0 < e →
      Integrable (fun v : ℂ => dmsShift γ z v *
        Real.circleAverage (fun u : ℂ => ((e : ℝ) ^ 2)⁻¹ * rho ((e : ℝ)⁻¹ • (u - v))) w r)) ∧
    Tendsto (fun e : ℝ => ∫ v : ℂ, dmsShift γ z v *
        Real.circleAverage (fun u : ℂ => ((e : ℝ) ^ 2)⁻¹ * rho ((e : ℝ)⁻¹ • (u - v))) w r)
      (𝓝[>] 0) (𝓝 (-γ * Real.log (max r ‖w - z‖) + γ * Real.circleAverage logMaxOne w r)) := by
  show (∀ e : ℝ, 0 < e →
      Integrable (fun v : ℂ => dmsShift γ z v *
        Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r)) ∧
    Tendsto (fun e : ℝ => ∫ v : ℂ, dmsShift γ z v *
        Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r)
      (𝓝[>] 0) (𝓝 (-γ * Real.log (max r ‖w - z‖) + γ * Real.circleAverage logMaxOne w r))
  have hc : Continuous rho := h_smooth.continuous
  have hgl : LocallyIntegrable (fun v : ℂ => Real.log ‖v - z‖) :=
    locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm z
  have hgm : Measurable (fun v : ℂ => Real.log ‖v - z‖) :=
    Real.measurable_log.comp (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
  have hlm : LocallyIntegrable logMaxOne := continuous_logMaxOne.locallyIntegrable
  have hlmm : Measurable logMaxOne := continuous_logMaxOne.measurable
  have hI1 : ∀ e : ℝ, 0 < e → Integrable (fun v : ℂ =>
      Real.log ‖v - z‖ * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r) := fun e he =>
    integrable_mul_of_zero_outside (c := w) (R := r + e) hgl hgm
      (continuous_circleAverage_mollifierAt hc w r e)
      (fun v hv => circleAverage_mollifierAt_eq_zero h_supp w hr he hv)
  have hI2 : ∀ e : ℝ, 0 < e → Integrable (fun v : ℂ =>
      logMaxOne v * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r) := fun e he =>
    integrable_mul_of_zero_outside (c := w) (R := r + e) hlm hlmm
      (continuous_circleAverage_mollifierAt hc w r e)
      (fun v hv => circleAverage_mollifierAt_eq_zero h_supp w hr he hv)
  -- pointwise splitting of the DMS shift into the log-singular and the continuous part
  have hpt : ∀ e : ℝ, ∀ v : ℂ,
      dmsShift γ z v * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r
        = (-γ) * (Real.log ‖v - z‖ * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r)
          + γ * (logMaxOne v * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r) := by
    intro e v
    unfold dmsShift logMaxOne
    rw [max_comm ‖v‖ 1]
    ring
  have hJ1 : ∀ e : ℝ, 0 < e →
      ∫ v : ℂ, Real.log ‖v - z‖ * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r
        = ∫ y : ℂ, mollifierAt rho e y * Real.log (max r ‖(y + z) - w‖) := by
    intro e he
    refine (integral_mul_circleAverage_mollifierAt h_supp hc hgm hgl w hr he).trans ?_
    congr 1
    funext y
    congr 1
    exact circleAverage_log_sub y z w hr
  have hJ2 : ∀ e : ℝ, 0 < e →
      ∫ v : ℂ, logMaxOne v * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r
        = ∫ y : ℂ, mollifierAt rho e y * Real.circleAverage logMaxOne (w - y) r := by
    intro e he
    refine (integral_mul_circleAverage_mollifierAt h_supp hc hlmm hlm w hr he).trans ?_
    congr 1
    funext y
    congr 1
    exact circleAverage_comp_sub logMaxOne w y r
  have hdec : ∀ e : ℝ, 0 < e →
      ∫ v : ℂ, dmsShift γ z v * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r
        = (-γ) * (∫ y : ℂ, mollifierAt rho e y * Real.log (max r ‖(y + z) - w‖))
          + γ * (∫ y : ℂ, mollifierAt rho e y * Real.circleAverage logMaxOne (w - y) r) := by
    intro e he
    simp_rw [hpt e]
    rw [integral_add ((hI1 e he).const_mul (-γ)) ((hI2 e he).const_mul γ), integral_const_mul,
      integral_const_mul, hJ1 e he, hJ2 e he]
  have hT1 : Tendsto (fun e : ℝ => ∫ y : ℂ, mollifierAt rho e y * Real.log (max r ‖(y + z) - w‖))
      (𝓝[>] 0) (𝓝 (Real.log (max r ‖(0 + z) - w‖))) :=
    tendsto_integral_mollifierAt_mul hc h_nonneg h_supp h_one (continuous_log_max_sub w z hr)
  have hT2 : Tendsto (fun e : ℝ => ∫ y : ℂ, mollifierAt rho e y * Real.circleAverage logMaxOne (w - y) r)
      (𝓝[>] 0) (𝓝 (Real.circleAverage logMaxOne (w - 0) r)) :=
    tendsto_integral_mollifierAt_mul hc h_nonneg h_supp h_one (continuous_circleAverage_logMaxOne_sub w r)
  have hlim : Tendsto (fun e : ℝ =>
      (-γ) * (∫ y : ℂ, mollifierAt rho e y * Real.log (max r ‖(y + z) - w‖))
        + γ * (∫ y : ℂ, mollifierAt rho e y * Real.circleAverage logMaxOne (w - y) r))
      (𝓝[>] 0) (𝓝 ((-γ) * Real.log (max r ‖(0 + z) - w‖) + γ * Real.circleAverage logMaxOne (w - 0) r)) :=
    (hT1.const_mul (-γ)).add (hT2.const_mul γ)
  have h10 : Real.log (max r ‖(0 + z) - w‖) = Real.log (max r ‖w - z‖) := by
    rw [zero_add, norm_sub_rev]
  have h20 : Real.circleAverage logMaxOne (w - 0) r = Real.circleAverage logMaxOne w r := by
    rw [sub_zero]
  rw [h10, h20] at hlim
  refine ⟨fun e he => ?_, ?_⟩
  · exact (((hI1 e he).const_mul (-γ)).add ((hI2 e he).const_mul γ)).congr
      (ae_of_all _ fun v => (hpt e v).symm)
  · refine Tendsto.congr' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with e he
    exact (hdec e (Set.mem_Ioi.1 he)).symm

end HarmonicBalls

import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedLogCircleLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedContinuousCircleLimit
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteACircleSmooth
import HarmonicBalls.Proofs.Sec11.ClosureScales.RootedShiftProfile
import HarmonicBalls.Proofs.Potential.Fundamental

/-!
# L² convergence of the literal mollified circle pairing for the whole-plane GFF

Section 11 closure, the L² input of the circle-code statement. Fixed circle `∂B_r(w)` with `r > 0`, a literal mollifier
`ρ` (even, nonnegative, smooth, supported in `closedBall 0 1`, mass one) and
`φ_ε(v) = ⨍_{∂B_r(w)} ε⁻² ρ(ε⁻¹ (x - v)) dx`.

* `isTestFunction_circleMollifier`: `φ_ε` is a smooth compactly supported test function for every `ε > 0`.
* `tendsto_integral_circleMollifier_mul`: for continuous `u`, `∫ u φ_ε → ⨍_{∂B_r(w)} u` (approximate identity on
  the circle, from `mollified_continuous_circle_limit`).
* Kernel. Off the diagonal, `wholePlaneCov x y = L x + L y - log|x - y|` with `L = logMaxOne`. The circle potential
  `P(p) = log max(r, |p - w|)` is `1/r`-Lipschitz (Mathlib's mean value identity for `log|·|`, through
  `circleAverage_log_sub`). Moving the mollifier onto `P` (Fubini, `integral_mul_circleAverage_mollifierAt`) gives
  the mollified potential `J_ε(x) = ∫ mollifierAt(y) P(y + x) dy`, which is within `ε/r` of `P(x)`.
* `tendsto_wholePlaneGFFCov_pairing_pairing` and `tendsto_wholePlaneGFFCov_pairing_circle`: the two kernel limits,
  both to `wholePlaneGFFCov (circle r w) (circle r w)`.
* `isWholePlaneGFF_circleMollifier_L2`: for the whole-plane GFF, `hC ω φ_ε - hcirc ω r w` lies in `L²(P)` and its second
  moment tends to `0` as `ε ↓ 0`, by expanding the square into the two variances and the mixed covariance.

Terminology: the whole-plane GFF and its covariance are those of Duplantier-Sheffield (`Defs/GFF.lean`); the logarithmic
potential of the circle is the mean value identity of potential theory (Armitage-Gardiner), via `circleAverage_log_sub`.

No external input, no new hypothesis: the hypotheses on `ρ` are the five conditions of the circle-code statement, packaged as
`IsLiteralMollifier`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ContDiff

/-- The hypotheses on the literal mollifier `ρ` of the circle-code statement: even, nonnegative, smooth, supported in
`closedBall 0 1`, with integral one. -/
structure IsLiteralMollifier (rho : ℂ → ℝ) : Prop where
  even : ∀ x : ℂ, rho (-x) = rho x
  nonneg : ∀ x : ℂ, 0 ≤ rho x
  smooth : ContDiff ℝ ∞ rho
  supp : tsupport rho ⊆ closedBall (0 : ℂ) 1
  mass : ∫ x : ℂ, rho x = 1

/-- The literal mollified circle average `φ_ε(v) = ⨍_{∂B_r(w)} (ε²)⁻¹ ρ(ε⁻¹ • (x - v)) dx`. -/
noncomputable def circleMollifier (rho : ℂ → ℝ) (w : ℂ) (r e : ℝ) (v : ℂ) : ℝ :=
  Real.circleAverage (fun x : ℂ => (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • (x - v))) w r

/-- The circle potential `p ↦ log max(r, |p - w|)`, the logarithmic potential of the uniform measure on `∂B_r(w)`. -/
noncomputable def circlePot (w : ℂ) (r : ℝ) (p : ℂ) : ℝ :=
  Real.log (max r ‖p - w‖)

/-- The mollified circle potential `x ↦ ∫ mollifierAt(y) P(y + x) dy`. -/
noncomputable def mollifiedPot (rho : ℂ → ℝ) (w : ℂ) (r e : ℝ) (x : ℂ) : ℝ :=
  ∫ y : ℂ, mollifierAt rho e y * circlePot w r (y + x)

/-- The circle average of the covariance kernel, `x ↦ ⨍_{∂B_r(w)} wholePlaneCov(x, ·)`, in closed form. -/
noncomputable def circleKernelMean (w : ℂ) (r : ℝ) (x : ℂ) : ℝ :=
  logMaxOne x + Real.circleAverage logMaxOne w r - circlePot w r x

section Mollifier

lemma circleMollifier_eq (rho : ℂ → ℝ) (w : ℂ) (r e : ℝ) (v : ℂ) :
    circleMollifier rho w r e v =
      Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r :=
  circleAverage_kernel_eq rho e v w r

lemma circleMollifier_nonneg {rho : ℂ → ℝ} (h0 : ∀ x : ℂ, 0 ≤ rho x) (w : ℂ) (r e : ℝ) (v : ℂ) :
    0 ≤ circleMollifier rho w r e v := by
  unfold circleMollifier
  exact Real.circleAverage_nonneg_of_nonneg fun x _ => mul_nonneg (zpow_nonneg (sq_nonneg e) _) (h0 _)

lemma isTestFunction_circleMollifier {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {w : ℂ} {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) : IsTestFunction univ (circleMollifier rho w r e) := by
  have hm : ContDiff ℝ ∞ (mollifierAt rho e) := by
    unfold mollifierAt
    exact contDiff_const.mul (hρ.smooth.comp (contDiff_id.const_smul e⁻¹))
  refine ⟨?_, ?_, subset_univ _⟩
  · have hfun : circleMollifier rho w r e =
        fun v : ℂ => Real.circleAverage (mollifierAt rho e) (w - v) r := by
      funext v
      rw [circleMollifier_eq, circleAverage_comp_sub (mollifierAt rho e) w v r]
    rw [hfun]
    exact (contDiff_circleAverage_of_contDiff hm (mollifierAt_hasCompactSupport hρ.supp he) r).comp
      (contDiff_const.sub contDiff_id)
  · refine HasCompactSupport.intro (isCompact_closedBall w (r + e)) fun v hv => ?_
    rw [circleMollifier_eq]
    exact circleAverage_mollifierAt_eq_zero hρ.supp w hr he hv

lemma tendsto_integral_circleMollifier_mul {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {u : ℂ → ℝ}
    (hu : Continuous u) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun e : ℝ => ∫ v : ℂ, u v * circleMollifier rho w r e v) (𝓝[>] 0)
      (𝓝 (Real.circleAverage u w r)) :=
  (mollified_continuous_circle_limit hρ.even hρ.nonneg hρ.smooth hρ.supp hρ.mass hu hr w).2

lemma tendsto_integral_circleMollifier {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (w : ℂ) {r : ℝ}
    (hr : 0 < r) : Tendsto (fun e : ℝ => ∫ v : ℂ, circleMollifier rho w r e v) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_integral_circleMollifier_mul hρ (u := fun _ : ℂ => (1 : ℝ)) continuous_const w hr
  simpa [Real.circleAverage_const] using h

end Mollifier

section Potential

lemma abs_log_sub_log_le_of_lower {a b r : ℝ} (hr : 0 < r) (ha : r ≤ a) (hb : r ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / r := by
  have ha0 : 0 < a := lt_of_lt_of_le hr ha
  have hb0 : 0 < b := lt_of_lt_of_le hr hb
  have hup : ∀ x y : ℝ, 0 < x → 0 < y → r ≤ y → Real.log x - Real.log y ≤ |x - y| / r := by
    intro x y hx hy hry
    rw [← Real.log_div hx.ne' hy.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
    have h2 : x / y - 1 = (x - y) / y := by rw [sub_div, div_self hy.ne']
    have h3 : (x - y) / y ≤ |x - y| / r :=
      (div_le_div_of_nonneg_right (le_abs_self _) hy.le).trans
        (div_le_div_of_nonneg_left (abs_nonneg _) hr hry)
    linarith
  have h1 := hup a b ha0 hb0 hb
  have h2 := hup b a hb0 ha0 ha
  rw [abs_sub_comm b a] at h2
  rw [abs_le]
  constructor <;> linarith

lemma abs_circlePot_sub_le (w : ℂ) {r : ℝ} (hr : 0 < r) (p q : ℂ) :
    |circlePot w r p - circlePot w r q| ≤ ‖p - q‖ / r := by
  unfold circlePot
  have hmax : |max r ‖p - w‖ - max r ‖q - w‖| ≤ ‖p - q‖ := by
    rw [max_comm r ‖p - w‖, max_comm r ‖q - w‖]
    calc |max ‖p - w‖ r - max ‖q - w‖ r| ≤ |‖p - w‖ - ‖q - w‖| := abs_max_sub_max_le_abs _ _ _
      _ ≤ ‖(p - w) - (q - w)‖ := abs_norm_sub_norm_le _ _
      _ = ‖p - q‖ := by congr 1; ring
  exact (abs_log_sub_log_le_of_lower hr (le_max_left _ _) (le_max_left _ _)).trans
    (div_le_div_of_nonneg_right hmax hr.le)

lemma continuous_circlePot (w : ℂ) {r : ℝ} (hr : 0 < r) : Continuous (circlePot w r) := by
  unfold circlePot
  exact Continuous.log (continuous_const.max (by fun_prop))
    fun p => (lt_of_lt_of_le hr (le_max_left _ _)).ne'

lemma circleIntegrable_of_continuousFn {f : ℂ → ℝ} (hf : Continuous f) (c : ℂ) (R : ℝ) :
    CircleIntegrable f c R :=
  (hf.comp (continuous_circleMap c R)).intervalIntegrable _ _

lemma circleIntegrable_log_norm_x_sub (x w : ℂ) (r : ℝ) :
    CircleIntegrable (fun y : ℂ => Real.log ‖x - y‖) w r := by
  have hfun : (fun y : ℂ => Real.log ‖x - y‖) = fun y : ℂ => Real.log ‖y - x‖ := by
    funext y
    rw [norm_sub_rev]
  rw [hfun]
  exact circleIntegrable_log_norm_sub_const (a := x) (c := w) r

end Potential

section LogInsertion

lemma integral_circleMollifier_mul_log_norm_sub {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {w : ℂ} {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) (x : ℂ) :
    ∫ y : ℂ, circleMollifier rho w r e y * Real.log ‖x - y‖ =
      ∫ y : ℂ, mollifierAt rho e y * circlePot w r (y + x) := by
  have hgl : LocallyIntegrable (fun v : ℂ => Real.log ‖v - x‖) :=
    locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
  have hgm : Measurable (fun v : ℂ => Real.log ‖v - x‖) := by fun_prop
  have key := integral_mul_circleAverage_mollifierAt hρ.supp hρ.smooth.continuous hgm hgl w hr he
  calc ∫ y : ℂ, circleMollifier rho w r e y * Real.log ‖x - y‖
      = ∫ y : ℂ, Real.log ‖y - x‖ * Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - y)) w r := by
        congr 1
        funext y
        rw [circleMollifier_eq, norm_sub_rev]
        ring
    _ = ∫ y : ℂ, mollifierAt rho e y * Real.circleAverage (fun u : ℂ => Real.log ‖u - y - x‖) w r := key
    _ = ∫ y : ℂ, mollifierAt rho e y * circlePot w r (y + x) := by
        congr 1
        funext y
        rw [circleAverage_log_sub y x w hr]
        rfl

lemma integrable_mollifier_mul_circlePot {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {e : ℝ} (he : 0 < e)
    {w : ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) :
    Integrable (fun y : ℂ => mollifierAt rho e y * circlePot w r (y + x)) := by
  have hc : Continuous (fun y : ℂ => mollifierAt rho e y * circlePot w r (y + x)) :=
    (mollifierAt_continuous hρ.smooth.continuous e).mul
      ((continuous_circlePot w hr).comp (continuous_id.add continuous_const))
  exact hc.integrable_of_hasCompactSupport ((mollifierAt_hasCompactSupport hρ.supp he).mul_right)

lemma integrable_mollifierAt {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {e : ℝ} (he : 0 < e) :
    Integrable (mollifierAt rho e) :=
  (mollifierAt_continuous hρ.smooth.continuous e).integrable_of_hasCompactSupport
    (mollifierAt_hasCompactSupport hρ.supp he)

lemma abs_mollifiedPot_sub_circlePot_le {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {e : ℝ} (he : 0 < e)
    {w : ℂ} {r : ℝ} (hr : 0 < r) (x : ℂ) :
    |mollifiedPot rho w r e x - circlePot w r x| ≤ e / r := by
  have hmass : ∫ y : ℂ, mollifierAt rho e y = 1 := mollifierAt_integral hρ.mass he
  have hm0 : ∀ y : ℂ, 0 ≤ mollifierAt rho e y := mollifierAt_nonneg hρ.nonneg e
  have hsplit : mollifiedPot rho w r e x - circlePot w r x =
      ∫ y : ℂ, mollifierAt rho e y * (circlePot w r (y + x) - circlePot w r x) := by
    unfold mollifiedPot
    have hI2 : Integrable (fun y : ℂ => mollifierAt rho e y * circlePot w r x) :=
      (integrable_mollifierAt hρ he).mul_const _
    simp_rw [mul_sub]
    rw [integral_sub (integrable_mollifier_mul_circlePot hρ he hr x) hI2, integral_mul_const, hmass, one_mul]
  rw [hsplit, ← Real.norm_eq_abs]
  calc ‖∫ y : ℂ, mollifierAt rho e y * (circlePot w r (y + x) - circlePot w r x)‖
      ≤ ∫ y : ℂ, mollifierAt rho e y * (e / r) := by
        refine norm_integral_le_of_norm_le ((integrable_mollifierAt hρ he).mul_const _)
          (ae_of_all _ fun y => ?_)
        show ‖mollifierAt rho e y * (circlePot w r (y + x) - circlePot w r x)‖ ≤ mollifierAt rho e y * (e / r)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm0 y)]
        rcases le_or_gt ‖y‖ e with hy | hy
        · refine mul_le_mul_of_nonneg_left ?_ (hm0 y)
          calc |circlePot w r (y + x) - circlePot w r x| ≤ ‖y + x - x‖ / r := abs_circlePot_sub_le w hr _ _
            _ = ‖y‖ / r := by rw [add_sub_cancel_right]
            _ ≤ e / r := div_le_div_of_nonneg_right hy hr.le
        · simp [mollifierAt_eq_zero hρ.supp he hy]
    _ = e / r := by rw [integral_mul_const, hmass, one_mul]

lemma abs_mollifiedPot_sub_mollifiedPot_le {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {e : ℝ} (he : 0 < e)
    {w : ℂ} {r : ℝ} (hr : 0 < r) (x x' : ℂ) :
    |mollifiedPot rho w r e x - mollifiedPot rho w r e x'| ≤ ‖x - x'‖ / r := by
  have hmass : ∫ y : ℂ, mollifierAt rho e y = 1 := mollifierAt_integral hρ.mass he
  have hm0 : ∀ y : ℂ, 0 ≤ mollifierAt rho e y := mollifierAt_nonneg hρ.nonneg e
  have hsplit : mollifiedPot rho w r e x - mollifiedPot rho w r e x' =
      ∫ y : ℂ, mollifierAt rho e y * (circlePot w r (y + x) - circlePot w r (y + x')) := by
    unfold mollifiedPot
    simp_rw [mul_sub]
    exact (integral_sub (integrable_mollifier_mul_circlePot hρ he hr x)
      (integrable_mollifier_mul_circlePot hρ he hr x')).symm
  rw [hsplit, ← Real.norm_eq_abs]
  calc ‖∫ y : ℂ, mollifierAt rho e y * (circlePot w r (y + x) - circlePot w r (y + x'))‖
      ≤ ∫ y : ℂ, mollifierAt rho e y * (‖x - x'‖ / r) := by
        refine norm_integral_le_of_norm_le ((integrable_mollifierAt hρ he).mul_const _)
          (ae_of_all _ fun y => ?_)
        show ‖mollifierAt rho e y * (circlePot w r (y + x) - circlePot w r (y + x'))‖ ≤
          mollifierAt rho e y * (‖x - x'‖ / r)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm0 y)]
        refine mul_le_mul_of_nonneg_left ?_ (hm0 y)
        calc |circlePot w r (y + x) - circlePot w r (y + x')| ≤ ‖(y + x) - (y + x')‖ / r :=
              abs_circlePot_sub_le w hr _ _
          _ = ‖x - x'‖ / r := by rw [add_sub_add_left_eq_sub]
    _ = ‖x - x'‖ / r := by rw [integral_mul_const, hmass, one_mul]

lemma continuous_mollifiedPot {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {e : ℝ} (he : 0 < e)
    {w : ℂ} {r : ℝ} (hr : 0 < r) : Continuous (mollifiedPot rho w r e) := by
  refine Metric.continuous_iff.2 fun x ε hε => ⟨ε * r, mul_pos hε hr, fun x' hx' => ?_⟩
  rw [Real.dist_eq]
  have h := abs_mollifiedPot_sub_mollifiedPot_le (w := w) hρ he hr x' x
  rw [dist_eq_norm] at hx'
  exact h.trans_lt ((div_lt_iff₀ hr).2 hx')

lemma integrable_circleMollifier_mul_log_norm_x_sub {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {w : ℂ}
    {r : ℝ} (hr : 0 < r) {e : ℝ} (he : 0 < e) (x : ℂ) :
    Integrable (fun y : ℂ => circleMollifier rho w r e y * Real.log ‖x - y‖) := by
  have hφ := isTestFunction_circleMollifier (w := w) hρ hr he
  have hgl : LocallyIntegrable (fun v : ℂ => Real.log ‖v - x‖) :=
    locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
  have hgm : Measurable (fun v : ℂ => Real.log ‖v - x‖) := by fun_prop
  have hz : ∀ y : ℂ, y ∉ closedBall w (r + e) → circleMollifier rho w r e y = 0 := fun y hy => by
    rw [circleMollifier_eq]
    exact circleAverage_mollifierAt_eq_zero hρ.supp w hr he hy
  refine (integrable_mul_of_zero_outside hgl hgm hφ.1.continuous hz).congr (ae_of_all _ fun y => ?_)
  show Real.log ‖y - x‖ * circleMollifier rho w r e y = circleMollifier rho w r e y * Real.log ‖x - y‖
  rw [norm_sub_rev]
  ring

end LogInsertion

section Kernel

lemma wholePlaneCov_eq_of_ne {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov x y = logMaxOne x + logMaxOne y - Real.log ‖x - y‖ := by
  have hx : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hy : 0 < max 1 ‖y‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  unfold wholePlaneCov logMaxOne
  rw [max_comm ‖x‖ 1, max_comm ‖y‖ 1, Real.log_div (mul_pos hx hy).ne' hd.ne', Real.log_mul hx.ne' hy.ne']

lemma circleAverage_wholePlaneCov (w : ℂ) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    Real.circleAverage (fun y => wholePlaneCov x y) w r = circleKernelMean w r x := by
  have hcod : (fun y => wholePlaneCov x y) =ᶠ[codiscreteWithin (sphere w |r|)]
      fun y => (logMaxOne x + logMaxOne y) - Real.log ‖x - y‖ := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (s := sphere w |r|) x] with y hy
    exact wholePlaneCov_eq_of_ne (Set.mem_compl_singleton_iff.1 hy).symm
  rw [Real.circleAverage_congr_codiscreteWithin hcod hr.ne']
  have hf1 : CircleIntegrable (fun y : ℂ => logMaxOne x + logMaxOne y) w r :=
    circleIntegrable_of_continuousFn (continuous_const.add continuous_logMaxOne) w r
  have hf2 : CircleIntegrable (fun y : ℂ => Real.log ‖x - y‖) w r :=
    circleIntegrable_log_norm_x_sub x w r
  have hc : CircleIntegrable (fun _ : ℂ => logMaxOne x) w r :=
    circleIntegrable_of_continuousFn continuous_const w r
  have hL : CircleIntegrable logMaxOne w r := circleIntegrable_of_continuousFn continuous_logMaxOne w r
  have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖x - y‖) w r = circlePot w r x := by
    have hfun : (fun y : ℂ => Real.log ‖x - y‖) = fun u : ℂ => Real.log ‖u - x - 0‖ := by
      funext u
      rw [sub_zero, norm_sub_rev]
    rw [hfun, circleAverage_log_sub x 0 w hr, add_zero]
    rfl
  unfold circleKernelMean
  rw [Real.circleAverage_fun_sub hf1 hf2, Real.circleAverage_fun_add hc hL, Real.circleAverage_const, hlog]

lemma continuous_circleKernelMean (w : ℂ) {r : ℝ} (hr : 0 < r) : Continuous (circleKernelMean w r) := by
  unfold circleKernelMean
  exact (continuous_logMaxOne.add continuous_const).sub (continuous_circlePot w hr)

lemma wholePlaneGFFCov_circle_circle_eq (w : ℂ) {r : ℝ} (hr : 0 < r) :
    wholePlaneGFFCov (.circle r w) (.circle r w) = Real.circleAverage (circleKernelMean w r) w r := by
  show Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w r) w r = _
  congr 1
  funext x
  exact circleAverage_wholePlaneCov w hr x

lemma circleAverage_circleKernelMean (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (circleKernelMean w r) w r =
      2 * Real.circleAverage logMaxOne w r - Real.circleAverage (circlePot w r) w r := by
  have hf1 : CircleIntegrable (fun x : ℂ => logMaxOne x + Real.circleAverage logMaxOne w r) w r :=
    circleIntegrable_of_continuousFn (continuous_logMaxOne.add continuous_const) w r
  have hP : CircleIntegrable (circlePot w r) w r :=
    circleIntegrable_of_continuousFn (continuous_circlePot w hr) w r
  have hL : CircleIntegrable logMaxOne w r := circleIntegrable_of_continuousFn continuous_logMaxOne w r
  have hc : CircleIntegrable (fun _ : ℂ => Real.circleAverage logMaxOne w r) w r :=
    circleIntegrable_of_continuousFn continuous_const w r
  unfold circleKernelMean
  rw [Real.circleAverage_fun_sub hf1 hP, Real.circleAverage_fun_add hL hc, Real.circleAverage_const]
  ring

end Kernel

section Limits

lemma integral_circleMollifier_mul_wholePlaneCov {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {w : ℂ} {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) (x : ℂ) :
    ∫ y : ℂ, circleMollifier rho w r e y * wholePlaneCov x y =
      logMaxOne x * (∫ y : ℂ, circleMollifier rho w r e y) +
        (∫ y : ℂ, circleMollifier rho w r e y * logMaxOne y) - mollifiedPot rho w r e x := by
  have hφ := isTestFunction_circleMollifier (w := w) hρ hr he
  have hφc : Continuous (circleMollifier rho w r e) := hφ.1.continuous
  have hφs : HasCompactSupport (circleMollifier rho w r e) := hφ.2.1
  have hae : ∀ᵐ y ∂(volume : Measure ℂ), circleMollifier rho w r e y * wholePlaneCov x y =
      circleMollifier rho w r e y * (logMaxOne x + logMaxOne y - Real.log ‖x - y‖) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton x)] with y hy
    rw [wholePlaneCov_eq_of_ne (Set.mem_compl_singleton_iff.1 hy).symm]
  rw [integral_congr_ae hae]
  have h1 : Integrable (fun y : ℂ => logMaxOne x * circleMollifier rho w r e y) :=
    (hφc.integrable_of_hasCompactSupport hφs).const_mul _
  have h2 : Integrable (fun y : ℂ => circleMollifier rho w r e y * logMaxOne y) :=
    (hφc.mul continuous_logMaxOne).integrable_of_hasCompactSupport hφs.mul_right
  have h3 : Integrable (fun y : ℂ => circleMollifier rho w r e y * Real.log ‖x - y‖) :=
    integrable_circleMollifier_mul_log_norm_x_sub hρ hr he x
  have h12 : Integrable (fun y : ℂ => logMaxOne x * circleMollifier rho w r e y +
      circleMollifier rho w r e y * logMaxOne y) := h1.add h2
  have hfun : (fun y : ℂ => circleMollifier rho w r e y * (logMaxOne x + logMaxOne y - Real.log ‖x - y‖)) =
      fun y : ℂ => (logMaxOne x * circleMollifier rho w r e y + circleMollifier rho w r e y * logMaxOne y) -
        circleMollifier rho w r e y * Real.log ‖x - y‖ := by
    funext y
    ring
  rw [hfun, integral_sub h12 h3, integral_add h1 h2, integral_const_mul,
    integral_circleMollifier_mul_log_norm_sub hρ hr he x]
  rfl

lemma wholePlaneGFFCov_pairing_pairing_eq {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {w : ℂ} {r : ℝ}
    (hr : 0 < r) {e : ℝ} (he : 0 < e) :
    wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.pairing (circleMollifier rho w r e)) =
      2 * (∫ x : ℂ, circleMollifier rho w r e x) * (∫ x : ℂ, circleMollifier rho w r e x * logMaxOne x) -
        ∫ x : ℂ, circleMollifier rho w r e x * mollifiedPot rho w r e x := by
  have hφ := isTestFunction_circleMollifier (w := w) hρ hr he
  have hφc : Continuous (circleMollifier rho w r e) := hφ.1.continuous
  have hφs : HasCompactSupport (circleMollifier rho w r e) := hφ.2.1
  have hJc : Continuous (mollifiedPot rho w r e) := continuous_mollifiedPot hρ he hr
  show ∫ x : ℂ, circleMollifier rho w r e x *
      (∫ y : ℂ, circleMollifier rho w r e y * wholePlaneCov x y) = _
  simp_rw [integral_circleMollifier_mul_wholePlaneCov hρ hr he]
  have i1 : Integrable (fun x : ℂ => circleMollifier rho w r e x) :=
    hφc.integrable_of_hasCompactSupport hφs
  have i2 : Integrable (fun x : ℂ => circleMollifier rho w r e x * logMaxOne x) :=
    (hφc.mul continuous_logMaxOne).integrable_of_hasCompactSupport hφs.mul_right
  have i3 : Integrable (fun x : ℂ => circleMollifier rho w r e x * mollifiedPot rho w r e x) :=
    (hφc.mul hJc).integrable_of_hasCompactSupport hφs.mul_right
  have key : ∀ x : ℂ, circleMollifier rho w r e x *
      (logMaxOne x * (∫ y : ℂ, circleMollifier rho w r e y) +
        (∫ y : ℂ, circleMollifier rho w r e y * logMaxOne y) - mollifiedPot rho w r e x) =
      (∫ y : ℂ, circleMollifier rho w r e y) * (circleMollifier rho w r e x * logMaxOne x) +
        (∫ y : ℂ, circleMollifier rho w r e y * logMaxOne y) * circleMollifier rho w r e x -
        circleMollifier rho w r e x * mollifiedPot rho w r e x :=
    fun x => by ring
  simp_rw [key]
  have hX1 : Integrable (fun x : ℂ => (∫ y : ℂ, circleMollifier rho w r e y) *
      (circleMollifier rho w r e x * logMaxOne x)) := i2.const_mul _
  have hX2 : Integrable (fun x : ℂ => (∫ y : ℂ, circleMollifier rho w r e y * logMaxOne y) *
      circleMollifier rho w r e x) := i1.const_mul _
  have hX12 : Integrable (fun x : ℂ => (∫ y : ℂ, circleMollifier rho w r e y) *
      (circleMollifier rho w r e x * logMaxOne x) +
      (∫ y : ℂ, circleMollifier rho w r e y * logMaxOne y) * circleMollifier rho w r e x) := hX1.add hX2
  rw [integral_sub hX12 i3, integral_add hX1 hX2, integral_const_mul, integral_const_mul]
  ring

lemma tendsto_integral_circleMollifier_mul_mollifiedPot {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (w : ℂ)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun e : ℝ => ∫ x : ℂ, circleMollifier rho w r e x * mollifiedPot rho w r e x) (𝓝[>] 0)
      (𝓝 (Real.circleAverage (circlePot w r) w r)) := by
  have hP := tendsto_integral_circleMollifier_mul hρ (continuous_circlePot w hr) w hr
  have hmass := tendsto_integral_circleMollifier hρ w hr
  have hdiv : Tendsto (fun e : ℝ => e / r) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have h := (continuous_id.div_const r).tendsto (0 : ℝ)
    simpa using h
  have hbound : Tendsto (fun e : ℝ => (∫ x : ℂ, circleMollifier rho w r e x) * (e / r)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hmass.mul hdiv
  have herr : Tendsto (fun e : ℝ => ∫ x : ℂ, circleMollifier rho w r e x *
      (mollifiedPot rho w r e x - circlePot w r x)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [self_mem_nhdsWithin] with e he
    have he' : 0 < e := he
    have hφ := isTestFunction_circleMollifier (w := w) hρ hr he'
    have hφc : Continuous (circleMollifier rho w r e) := hφ.1.continuous
    have hφs : HasCompactSupport (circleMollifier rho w r e) := hφ.2.1
    have hI : Integrable (fun x : ℂ => circleMollifier rho w r e x) :=
      hφc.integrable_of_hasCompactSupport hφs
    calc ‖∫ x : ℂ, circleMollifier rho w r e x * (mollifiedPot rho w r e x - circlePot w r x)‖
        ≤ ∫ x : ℂ, circleMollifier rho w r e x * (e / r) := by
          refine norm_integral_le_of_norm_le (hI.mul_const _) (ae_of_all _ fun x => ?_)
          show ‖circleMollifier rho w r e x * (mollifiedPot rho w r e x - circlePot w r x)‖ ≤
            circleMollifier rho w r e x * (e / r)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (circleMollifier_nonneg hρ.nonneg w r e x)]
          exact mul_le_mul_of_nonneg_left (abs_mollifiedPot_sub_circlePot_le hρ he' hr x)
            (circleMollifier_nonneg hρ.nonneg w r e x)
      _ = (∫ x : ℂ, circleMollifier rho w r e x) * (e / r) := by rw [integral_mul_const]
  have hsum := herr.add hP
  rw [zero_add] at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with e he
  have he' : 0 < e := he
  have hφ := isTestFunction_circleMollifier (w := w) hρ hr he'
  have hφc : Continuous (circleMollifier rho w r e) := hφ.1.continuous
  have hφs : HasCompactSupport (circleMollifier rho w r e) := hφ.2.1
  have hi1 : Integrable (fun x : ℂ =>
      circleMollifier rho w r e x * (mollifiedPot rho w r e x - circlePot w r x)) :=
    (hφc.mul ((continuous_mollifiedPot hρ he' hr).sub (continuous_circlePot w hr))).integrable_of_hasCompactSupport
      hφs.mul_right
  have hi2 : Integrable (fun x : ℂ => circlePot w r x * circleMollifier rho w r e x) :=
    ((continuous_circlePot w hr).mul hφc).integrable_of_hasCompactSupport hφs.mul_left
  rw [← integral_add hi1 hi2]
  congr 1
  funext x
  ring

lemma tendsto_wholePlaneGFFCov_pairing_pairing {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (w : ℂ)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun e : ℝ => wholePlaneGFFCov (.pairing (circleMollifier rho w r e))
      (.pairing (circleMollifier rho w r e))) (𝓝[>] 0)
      (𝓝 (wholePlaneGFFCov (.circle r w) (.circle r w))) := by
  rw [wholePlaneGFFCov_circle_circle_eq w hr, circleAverage_circleKernelMean w hr]
  have hm := tendsto_integral_circleMollifier hρ w hr
  have hA : Tendsto (fun e : ℝ => ∫ x : ℂ, circleMollifier rho w r e x * logMaxOne x) (𝓝[>] 0)
      (𝓝 (Real.circleAverage logMaxOne w r)) :=
    Tendsto.congr (fun e => by congr 1; funext x; exact mul_comm _ _)
      (tendsto_integral_circleMollifier_mul hρ continuous_logMaxOne w hr)
  have hB := tendsto_integral_circleMollifier_mul_mollifiedPot hρ w hr
  have hlim := ((hm.const_mul 2).mul hA).sub hB
  rw [mul_one] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with e he
  have he' : 0 < e := he
  rw [wholePlaneGFFCov_pairing_pairing_eq hρ hr he']

lemma tendsto_wholePlaneGFFCov_pairing_circle {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) (w : ℂ)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun e : ℝ => wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.circle r w)) (𝓝[>] 0)
      (𝓝 (wholePlaneGFFCov (.circle r w) (.circle r w))) := by
  rw [wholePlaneGFFCov_circle_circle_eq w hr]
  have h := tendsto_integral_circleMollifier_mul hρ (continuous_circleKernelMean w hr) w hr
  refine Tendsto.congr (fun e => ?_) h
  show ∫ v : ℂ, circleKernelMean w r v * circleMollifier rho w r e v =
    ∫ x : ℂ, circleMollifier rho w r e x * Real.circleAverage (fun y => wholePlaneCov x y) w r
  congr 1
  funext x
  rw [circleAverage_wholePlaneCov w hr x, mul_comm]

end Limits

section Gaussian

lemma integral_sq_sub_eq_covariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hX0 : (∫ ξ, X ξ ∂P) = 0) (hY0 : (∫ ξ, Y ξ ∂P) = 0) :
    ∫ ξ, (X ξ - Y ξ) ^ 2 ∂P = covariance X X P - 2 * covariance X Y P + covariance Y Y P := by
  have hXX : covariance X X P = ∫ ξ, X ξ * X ξ ∂P := by
    unfold covariance
    rw [hX0]
    congr 1
    funext ξ
    ring
  have hXY : covariance X Y P = ∫ ξ, X ξ * Y ξ ∂P := by
    unfold covariance
    rw [hX0, hY0]
    congr 1
    funext ξ
    ring
  have hYY : covariance Y Y P = ∫ ξ, Y ξ * Y ξ ∂P := by
    unfold covariance
    rw [hY0]
    congr 1
    funext ξ
    ring
  rw [hXX, hXY, hYY]
  have h1 : Integrable (fun ξ => X ξ * X ξ) P := hX.integrable_mul hX
  have h2 : Integrable (fun ξ => X ξ * Y ξ) P := hX.integrable_mul hY
  have h3 : Integrable (fun ξ => Y ξ * Y ξ) P := hY.integrable_mul hY
  have h4 : Integrable (fun ξ => X ξ * X ξ - 2 * (X ξ * Y ξ)) P := h1.sub (h2.const_mul 2)
  have hfun : (fun ξ => (X ξ - Y ξ) ^ 2) = fun ξ => (X ξ * X ξ - 2 * (X ξ * Y ξ)) + Y ξ * Y ξ := by
    funext ξ
    ring
  rw [hfun, integral_add h4 h3, integral_sub h1 (h2.const_mul 2), integral_const_mul]

/-- **Gaussian L² convergence of the literal mollified circle pairing** (the L² input). For a
whole-plane GFF `h` with pairings `hC` and circle averages `hcirc`, the random variables `⟨h, φ_ε⟩ - h_r(w)` are in
`L²(P)` for `ε > 0` and their second moments tend to `0` as `ε ↓ 0`. -/
theorem isWholePlaneGFF_circleMollifier_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (∀ e : ℝ, 0 < e → MemLp (fun ξ => hC ξ (circleMollifier rho w r e) - hcirc ξ r w) 2 P) ∧
      Tendsto (fun e : ℝ => ∫ ξ, (hC ξ (circleMollifier rho w r e) - hcirc ξ r w) ^ 2 ∂P)
        (𝓝[>] 0) (𝓝 0) := by
  have hadmC : ∀ e : ℝ, 0 < e → GFFObservable.IsAdmissible (.pairing (circleMollifier rho w r e)) :=
    fun e he => isTestFunction_circleMollifier (w := w) hρ hr he
  have hadmY : GFFObservable.IsAdmissible (.circle r w) := hr
  have hX : ∀ e : ℝ, 0 < e → MemLp (fun ξ => hC ξ (circleMollifier rho w r e)) 2 P := fun e he =>
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing (circleMollifier rho w r e), hadmC e he⟩ : GFFObservable.Admissible)).memLp_two
  have hY : MemLp (fun ξ => hcirc ξ r w) 2 P := (hGFF.hasGaussianLaw_circle hr w).memLp_two
  have hmeanX : ∀ e : ℝ, 0 < e → ∫ ξ, hC ξ (circleMollifier rho w r e) ∂P = 0 := fun e he =>
    hGFF.integral_eq_zero _ (hadmC e he)
  have hmeanY : ∫ ξ, hcirc ξ r w ∂P = 0 := hGFF.integral_eq_zero _ hadmY
  have hid : ∀ e : ℝ, 0 < e → ∫ ξ, (hC ξ (circleMollifier rho w r e) - hcirc ξ r w) ^ 2 ∂P =
      wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.pairing (circleMollifier rho w r e)) -
        2 * wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.circle r w) +
        wholePlaneGFFCov (.circle r w) (.circle r w) := by
    intro e he
    have h1 : covariance (fun ξ => hC ξ (circleMollifier rho w r e))
        (fun ξ => hC ξ (circleMollifier rho w r e)) P =
        wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.pairing (circleMollifier rho w r e)) :=
      hGFF.covariance_eq _ _ (hadmC e he) (hadmC e he)
    have h2 : covariance (fun ξ => hC ξ (circleMollifier rho w r e)) (fun ξ => hcirc ξ r w) P =
        wholePlaneGFFCov (.pairing (circleMollifier rho w r e)) (.circle r w) :=
      hGFF.covariance_eq _ _ (hadmC e he) hadmY
    have h3 : covariance (fun ξ => hcirc ξ r w) (fun ξ => hcirc ξ r w) P =
        wholePlaneGFFCov (.circle r w) (.circle r w) :=
      hGFF.covariance_eq _ _ hadmY hadmY
    rw [integral_sq_sub_eq_covariance (hX e he) hY (hmeanX e he) hmeanY, h1, h2, h3]
  refine ⟨fun e he => (hX e he).sub hY, ?_⟩
  have hΦ := tendsto_wholePlaneGFFCov_pairing_pairing hρ w hr
  have hΨ := tendsto_wholePlaneGFFCov_pairing_circle hρ w hr
  have hconst : Tendsto (fun _ : ℝ => wholePlaneGFFCov (.circle r w) (.circle r w)) (𝓝[>] 0)
      (𝓝 (wholePlaneGFFCov (.circle r w) (.circle r w))) := tendsto_const_nhds
  have hlim := (hΦ.sub (hΨ.const_mul 2)).add hconst
  have h0 : wholePlaneGFFCov (.circle r w) (.circle r w) - 2 * wholePlaneGFFCov (.circle r w) (.circle r w) +
      wholePlaneGFFCov (.circle r w) (.circle r w) = 0 := by ring
  rw [h0] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with e he
  have he' : 0 < e := he
  exact (hid e he').symm

end Gaussian

end HarmonicBalls

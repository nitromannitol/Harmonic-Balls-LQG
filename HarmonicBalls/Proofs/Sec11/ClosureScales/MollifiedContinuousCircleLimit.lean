import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedLogCircleLimit

/-!
# Deterministic continuous-addition limit of mollified circle averages


Let `rho : ℂ → ℝ` be even, nonnegative and smooth, with `tsupport rho ⊆ closedBall 0 1` and `∫ rho = 1`.
For `e > 0` the literal kernel `(e ^ 2) ^ (-1) * rho (e ^ (-1) • (x - v))` is the mollifier
`mollifierAt rho e (x - v)`, an approximate identity at scale `e`. For a continuous `u : ℂ → ℝ`, `r > 0`
and `w : ℂ`:

* (i) for every `e > 0`, `v ↦ u v * circleAverage (kernel e (· - v)) w r` is integrable;
* (ii) as `e → 0⁺` along the positive filter, `∫ v, u v * circleAverage (kernel e (· - v)) w r`
  tends to `circleAverage u w r`.

Route. Fubini (`integral_mul_circleAverage_mollifierAt`) rewrites the integral as
`∫ y, mollifierAt rho e y * circleAverage u (w - y) r`, using `circleAverage_comp_sub` for the inner average.
The centre map `y ↦ circleAverage u (w - y) r` is continuous, since `u` is continuous and the circle is compact
(parametric interval integral). The approximate-identity lemma `tendsto_integral_mollifierAt_mul` then gives the
limit at `y = 0`. Part (i) follows from the continuity of the kernel average in `v` and its vanishing outside
`closedBall w (r + e)`.

No boundedness, compact support, differentiability or integrability is assumed on `u`: continuity suffices
because the kernel has compact support for `e > 0`. The hypotheses `_h_even` and `h_smooth` are carried to match
the statement; the proof uses continuity of `rho`, nonnegativity, the support condition and `∫ rho = 1`. The
statement is pointwise in `u`, so it applies to sample-dependent continuous additions. Nothing here is random,
and no literature input or Lattice-Probability declaration is used.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace HarmonicBalls

/-- The literal kernel `(e ^ 2) ^ (-1) * rho (e ^ (-1) • x)` is the mollifier `mollifierAt rho e x`. -/
lemma kernel_eq_mollifierAt (rho : ℂ → ℝ) (e : ℝ) (x : ℂ) :
    (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • x) = mollifierAt rho e x := by
  rw [mollifierAt, zpow_neg_one, zpow_neg_one]

/-- Shifting the literal kernel to the point `v` gives the circle average of `mollifierAt rho e (· - v)`. -/
lemma circleAverage_kernel_eq (rho : ℂ → ℝ) (e : ℝ) (v w : ℂ) (r : ℝ) :
    Real.circleAverage (fun x : ℂ => (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • (x - v))) w r =
      Real.circleAverage (fun u : ℂ => mollifierAt rho e (u - v)) w r := by
  congr 1
  funext x
  exact kernel_eq_mollifierAt rho e (x - v)

/-- The circle average of a continuous function is continuous in the centre, for each fixed radius. -/
lemma continuous_circleAverage_center {u : ℂ → ℝ} (hu : Continuous u) (r : ℝ) :
    Continuous fun c : ℂ => Real.circleAverage u c r := by
  have hf : Continuous fun p : ℂ × ℝ => u (circleMap p.1 r p.2) := by
    unfold circleMap
    fun_prop
  have hI : Continuous fun c : ℂ => ∫ θ in (0 : ℝ)..(2 * Real.pi), u (circleMap c r θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (c : ℂ) (θ : ℝ) => u (circleMap c r θ)) hf 0 (2 * Real.pi)
  unfold Real.circleAverage
  simp only [smul_eq_mul]
  exact continuous_const.mul hI

/-- (i) For `e > 0` the integrand of the continuous-addition limit is integrable. -/
lemma integrable_mul_circleAverage_kernel {rho : ℂ → ℝ} (hc : Continuous rho)
    (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) {u : ℂ → ℝ} (hu : Continuous u)
    {r : ℝ} (hr : 0 < r) (w : ℂ) {e : ℝ} (he : 0 < e) :
    Integrable (fun v : ℂ => u v * Real.circleAverage
      (fun x : ℂ => (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • (x - v))) w r) := by
  simp only [circleAverage_kernel_eq]
  exact integrable_mul_of_zero_outside (g := u)
    (φ := fun v : ℂ => Real.circleAverage (fun x : ℂ => mollifierAt rho e (x - v)) w r)
    (c := w) (R := r + e) hu.locallyIntegrable hu.measurable
    (continuous_circleAverage_mollifierAt hc w r e)
    (fun x hx => circleAverage_mollifierAt_eq_zero h_supp w hr he hx)

/-- (ii) As `e → 0⁺` the mollified circle averages of a continuous `u` integrate to the circle average of `u`
(approximate identity at the centre `w`). -/
lemma tendsto_mul_circleAverage_kernel {rho : ℂ → ℝ} (hc : Continuous rho)
    (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1) (h0 : ∀ x : ℂ, 0 ≤ rho x)
    (hint : ∫ x : ℂ, rho x = 1) {u : ℂ → ℝ} (hu : Continuous u) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    Tendsto (fun e : ℝ => ∫ v : ℂ, u v * Real.circleAverage
      (fun x : ℂ => (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • (x - v))) w r)
      (𝓝[>] 0) (𝓝 (Real.circleAverage u w r)) := by
  have hw : Continuous fun y : ℂ => w - y := continuous_const.sub continuous_id
  have hh : Continuous fun y : ℂ => Real.circleAverage u (w - y) r :=
    (continuous_circleAverage_center hu r).comp hw
  have hlim := tendsto_integral_mollifierAt_mul hc h0 h_supp hint hh
  rw [sub_zero] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with e he
  have he' : 0 < e := Set.mem_Ioi.mp he
  simp only [circleAverage_kernel_eq]
  rw [integral_mul_circleAverage_mollifierAt h_supp hc hu.measurable hu.locallyIntegrable w hr he']
  congr 1
  funext y
  rw [circleAverage_comp_sub]

/-- **Deterministic continuous-addition limit**. Let `rho` be even,
nonnegative and smooth with `tsupport rho ⊆ closedBall 0 1` and `∫ rho = 1`. For a continuous `u : ℂ → ℝ`,
`r > 0` and `w : ℂ`: (i) for each `e > 0` the integrand is integrable; (ii) its integral tends to
`circleAverage u w r` as `e → 0⁺`. No boundedness, compact support or integrability is assumed on `u`. -/
theorem mollified_continuous_circle_limit {rho : ℂ → ℝ}
    (_h_even : ∀ x : ℂ, rho (-x) = rho x) (h0 : ∀ x : ℂ, 0 ≤ rho x)
    (h_smooth : ContDiff ℝ ∞ rho) (h_supp : tsupport rho ⊆ closedBall (0 : ℂ) 1)
    (hint : ∫ x : ℂ, rho x = 1) {u : ℂ → ℝ} (hu : Continuous u) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (∀ e : ℝ, 0 < e → Integrable (fun v : ℂ => u v * Real.circleAverage
      (fun x : ℂ => (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • (x - v))) w r)) ∧
    Tendsto (fun e : ℝ => ∫ v : ℂ, u v * Real.circleAverage
      (fun x : ℂ => (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • (x - v))) w r)
      (𝓝[>] 0) (𝓝 (Real.circleAverage u w r)) :=
  ⟨fun _ he => integrable_mul_circleAverage_kernel h_smooth.continuous h_supp hu hr w he,
    tendsto_mul_circleAverage_kernel h_smooth.continuous h_supp h0 hint hu hr w⟩

end HarmonicBalls

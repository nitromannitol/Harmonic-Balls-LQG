import Mathlib
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.Frozen.S11i

/-!
# Singular Weyl change of the γ-LQG measure (write-up Step 12, identities (1)-(2))

Source: `notes/fp-gaps/CHATGPT-n3-step12-gaps.md` §1-§2 (identities (1), (2)); HB Fact 2.1 (I) (nonatomicity),
printed p. 9. For `0 < γ < 2` and `α < Q`, almost surely `μ_α = |z|^{-γα} μ_0` as measures on `ℂ`, and the two
measures have the same null sets. The write-up's Weyl-scaling input `LQGMeasureWeylScaling` is not used.

Route:
* For `0 < r < |z|` the circle average of `log ‖·‖` over the circle of radius `r` about `z` equals `log |z|`
  (Jensen; Mathlib `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). Hence the field circle averages
  satisfy `h_ε(z) = h^ℂ_ε(z) - α log|z|` for `ε < |z|`, and the approximations differ by the factor `w(z)`.
* Test functions vanishing near `0` transfer the vague limits (`IsLQGLimit`).
* Cut-offs `c_n` with monotone convergence extend the identity to all compactly supported continuous
  functions, using that both measures have no atom at `0`.
* `Measure.ext_of_integral_eq_on_compactlySupported` gives equality of measures.
Measurability of the approximating densities in `z` is the frozen input `CircleAverageVersionMeasurableStmt`.
-/

namespace HarmonicBalls.SingularWeyl

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

/-- The Weyl factor `w(z) = exp (-(γ α) · log ‖z‖)`: equal to `‖z‖ ^ (-γ α)` for `z ≠ 0` and `1` at `0`
(Lean's convention `Real.log 0 = 0`). Write-up Step 12, identity (1). -/
noncomputable def weylFactor (γ α : ℝ) (z : ℂ) : ℝ :=
  Real.exp (-(γ * α) * Real.log ‖z‖)

lemma weylFactor_pos (γ α : ℝ) (z : ℂ) : 0 < weylFactor γ α z :=
  Real.exp_pos _

lemma weylFactor_measurable (γ α : ℝ) : Measurable (weylFactor γ α) := by
  unfold weylFactor
  fun_prop

lemma weylFactor_continuousAt {γ α : ℝ} {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (weylFactor γ α) z := by
  have hlog : ContinuousAt (fun x : ℂ => Real.log ‖x‖) z :=
    ContinuousAt.log continuous_norm.continuousAt (norm_ne_zero_iff.2 hz)
  unfold weylFactor
  exact Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hlog)

/-- Mean value property of `log ‖·‖` on a circle not enclosing `0`: for `0 < r < |z|` the circle average of
`log |x|` over `∂B_r(z)` is `log |z|` (Jensen's formula, Mathlib). -/
lemma circleAverage_log_norm_eq {z : ℂ} {r : ℝ} (hr : 0 < r) (hrz : r < ‖z‖) :
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r = Real.log ‖z‖ := by
  have hz : 0 < ‖z‖ := hr.trans hrz
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) hr.ne'
  simp only [sub_zero] at h
  have hge : 1 ≤ r⁻¹ * ‖z‖ := by
    rw [← div_eq_inv_mul, one_le_div hr]
    exact hrz.le
  rw [h, Real.posLog_eq_log (by rw [abs_of_nonneg (zero_le_one.trans hge)]; exact hge),
    Real.log_mul (inv_ne_zero hr.ne') hz.ne', Real.log_inv]
  ring

/-- The field circle averages of `h = h^ℂ - α log|·|` and of `h^ℂ` differ by `α log|z|` for `0 < r < |z|`. -/
lemma fieldCircleAverage_eq_sub {α : ℝ} {hc : ℝ → ℂ → ℝ} {r : ℝ} {z : ℂ} (hr : 0 < r) (hrz : r < ‖z‖) :
    fieldCircleAverage α hc r z = fieldCircleAverage 0 hc r z - α * Real.log ‖z‖ := by
  unfold fieldCircleAverage
  rw [circleAverage_log_norm_eq hr hrz]
  ring

/-- The field circle average `z ↦ fieldCircleAverage α hc r z` is measurable when `hc r` is, for `r > 0`
(the logarithmic term is `log r + log⁺(r⁻¹ |z|)` by Jensen's formula). -/
lemma measurable_fieldCircleAverage {α : ℝ} {hc : ℝ → ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hm : Measurable (hc r)) : Measurable (fun z : ℂ => fieldCircleAverage α hc r z) := by
  have hJ : ∀ z : ℂ, Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r =
      Real.log r + Real.posLog (r⁻¹ * ‖z‖) := by
    intro z
    have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) hr.ne'
    simpa only [sub_zero] using h
  have hL : Measurable (fun z : ℂ => Real.log r + Real.posLog (r⁻¹ * ‖z‖)) :=
    measurable_const.add (Real.continuous_posLog.measurable.comp (measurable_const.mul measurable_norm))
  have heq : (fun z : ℂ => fieldCircleAverage α hc r z) =
      fun z : ℂ => hc r z - α * (Real.log r + Real.posLog (r⁻¹ * ‖z‖)) := by
    funext z
    unfold fieldCircleAverage
    rw [hJ z]
  rw [heq]
  exact hm.sub (measurable_const.mul hL)

/-- The Lebesgue density integral of the approximation `ε^{γ²/2} e^{γ h_ε(z)} dz`. -/
lemma integral_lqgApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℝ} (hε0 : 0 ≤ ε) (hm : Measurable (hε ε))
    (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ hε ε) = ∫ z, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z) * f z := by
  unfold lqgApprox
  have hmeas : Measurable (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hm)))
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  rw [smul_eq_mul, ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hε0 _) (Real.exp_pos _).le)]

/-- Continuity of `z ↦ f(z) w(z)` when `f` vanishes on a ball about `0`. -/
lemma continuous_mul_weylFactor {γ α δ : ℝ} {f : ℂ → ℝ} (hf : Continuous f) (hδ : 0 < δ)
    (hfδ : ∀ z : ℂ, ‖z‖ < δ → f z = 0) : Continuous (fun z => f z * weylFactor γ α z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    refine (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℝ)) 0).congr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with x hx
    rw [mem_ball_zero_iff] at hx
    simp [hfδ x hx]
  · exact hf.continuousAt.mul (weylFactor_continuousAt hz)

/-- Test identity: for `f` continuous with compact support, vanishing on `B_δ(0)`, the vague limits give
`∫ f dμ_α = ∫ f w dμ_0`. -/
lemma integral_test_eq {γ α δ : ℝ} {hg hh : ℝ → ℂ → ℝ} {m0 mα : Measure ℂ}
    (hcomp : ∀ r z, 0 < r → r < ‖z‖ → hh r z = hg r z - α * Real.log ‖z‖)
    (hgm : ∀ k : ℕ, Measurable (hg (dyadicScale k)))
    (hhm : ∀ k : ℕ, Measurable (hh (dyadicScale k)))
    (hg_lim : IsLQGLimit γ hg m0) (hh_lim : IsLQGLimit γ hh mα)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hδ : 0 < δ)
    (hfδ : ∀ z : ℂ, ‖z‖ < δ → f z = 0) :
    ∫ z, f z ∂mα = ∫ z, f z * weylFactor γ α z ∂m0 := by
  have hfw : Continuous (fun z => f z * weylFactor γ α z) := continuous_mul_weylFactor hf hδ hfδ
  have hfws : HasCompactSupport (fun z => f z * weylFactor γ α z) := hfs.mul_right
  have hev : ∀ᶠ k : ℕ in atTop, dyadicScale k < δ := by
    have h0 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact h0.eventually (gt_mem_nhds hδ)
  have heq : (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ hh (dyadicScale k))) =ᶠ[atTop]
      (fun k : ℕ => ∫ z, f z * weylFactor γ α z ∂(lqgApprox γ hg (dyadicScale k))) := by
    filter_upwards [hev] with k hk
    rw [integral_lqgApprox (dyadicScale_pos k).le (hhm k) f,
      integral_lqgApprox (dyadicScale_pos k).le (hgm k)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : ‖z‖ < δ
    · simp [hfδ z hz]
    · have hz' : δ ≤ ‖z‖ := not_lt.1 hz
      have hεz : dyadicScale k < ‖z‖ := lt_of_lt_of_le hk hz'
      have hexp : Real.exp (γ * hh (dyadicScale k) z) =
          Real.exp (γ * hg (dyadicScale k) z) * weylFactor γ α z := by
        rw [hcomp _ z (dyadicScale_pos k) hεz, weylFactor, ← Real.exp_add]
        congr 1
        ring
      simp only [hexp]
      ring
  have h1 := hh_lim.tendsto_integral f hf hfs
  have h2 := hg_lim.tendsto_integral (fun z => f z * weylFactor γ α z) hfw hfws
  exact tendsto_nhds_unique h1 (Tendsto.congr' heq.symm h2)

/-- Cut-off `c_n(z) = min 1 (max 0 ((n+1)‖z‖ - 1))`: continuous, with values in `[0, 1]`, zero on
`‖z‖ < 1/(n+1)`, nondecreasing in `n`, and equal to `1` for large `n` when `z ≠ 0`. -/
noncomputable def cutoff (n : ℕ) (z : ℂ) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * ‖z‖ - 1))

lemma continuous_cutoff (n : ℕ) : Continuous (cutoff n) := by
  unfold cutoff
  fun_prop

lemma cutoff_nonneg (n : ℕ) (z : ℂ) : 0 ≤ cutoff n z :=
  le_min zero_le_one (le_max_left _ _)

lemma cutoff_eq_zero {n : ℕ} {z : ℂ} (h : ((n : ℝ) + 1) * ‖z‖ < 1) : cutoff n z = 0 := by
  unfold cutoff
  rw [max_eq_left (by linarith), min_eq_right zero_le_one]

lemma cutoff_mono (z : ℂ) : Monotone (fun n : ℕ => cutoff n z) := by
  intro n m hnm
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
  have h1 : ((n : ℝ) + 1) * ‖z‖ ≤ ((m : ℝ) + 1) * ‖z‖ :=
    mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg z)
  unfold cutoff
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

lemma tendsto_cutoff {z : ℂ} (hz : z ≠ 0) : Tendsto (fun n : ℕ => cutoff n z) atTop (𝓝 1) := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈2 / ‖z‖⌉₊] with n hn
  have h2 : 2 / ‖z‖ ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 hn)
  have h3 : 2 ≤ (n : ℝ) * ‖z‖ := (div_le_iff₀ hpos).1 h2
  unfold cutoff
  rw [max_eq_right (by nlinarith), min_eq_left (by nlinarith)]

/-- Bump function `b_x(z) = max 0 (min 1 (2 - dist z x))`: `1` on `B̄_1(x)`, `0` off `B̄_2(x)`. -/
noncomputable def bumpBall (x z : ℂ) : ℝ :=
  max 0 (min 1 (2 - dist z x))

lemma continuous_bumpBall (x : ℂ) : Continuous (bumpBall x) := by
  unfold bumpBall
  fun_prop

lemma bumpBall_nonneg (x z : ℂ) : 0 ≤ bumpBall x z :=
  le_max_left _ _

lemma bumpBall_one {x z : ℂ} (h : dist z x ≤ 1) : bumpBall x z = 1 := by
  unfold bumpBall
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma hasCompactSupport_bumpBall (x : ℂ) : HasCompactSupport (bumpBall x) := by
  refine HasCompactSupport.intro (isCompact_closedBall x 2) fun z hz => ?_
  have h : 2 < dist z x := by simpa [Metric.mem_closedBall, not_le] using hz
  unfold bumpBall
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

lemma integrable_of_lintegral_ofReal {m : Measure ℂ} {g : ℂ → ℝ} (hg : Measurable g)
    (hg0 : ∀ z, 0 ≤ g z) (h : ∫⁻ z, ENNReal.ofReal (g z) ∂m ≠ ⊤) : Integrable g m :=
  ⟨hg.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)).2 (lt_top_iff_ne_top.2 h)⟩

lemma lintegral_ofReal_ne_top_of_integrable {m : Measure ℂ} {g : ℂ → ℝ} (hg : Integrable g m)
    (hg0 : ∀ z, 0 ≤ g z) : ∫⁻ z, ENNReal.ofReal (g z) ∂m ≠ ⊤ :=
  ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hg0)).1 hg.2).ne

lemma hasCompactSupport_of_zeros {f g : ℂ → ℝ} (hfs : HasCompactSupport f)
    (h : ∀ z, f z = 0 → g z = 0) : HasCompactSupport g :=
  HasCompactSupport.intro hfs.isCompact fun z hz => h z (image_eq_zero_of_notMem_tsupport hz)

/-- Nonnegative case, in lintegral form: `∫⁻ f dμ_α = ∫⁻ f w dμ_0` for `f ≥ 0` continuous with compact support. -/
lemma lintegral_eq_of_nonneg {γ α : ℝ} {hg hh : ℝ → ℂ → ℝ} {m0 mα : Measure ℂ}
    [IsLocallyFiniteMeasure m0] [IsLocallyFiniteMeasure mα]
    (hcomp : ∀ r z, 0 < r → r < ‖z‖ → hh r z = hg r z - α * Real.log ‖z‖)
    (hgm : ∀ k : ℕ, Measurable (hg (dyadicScale k)))
    (hhm : ∀ k : ℕ, Measurable (hh (dyadicScale k)))
    (hg_lim : IsLQGLimit γ hg m0) (hh_lim : IsLQGLimit γ hh mα)
    (h0g : m0 {0} = 0) (h0h : mα {0} = 0)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : ∀ z, 0 ≤ f z) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂mα = ∫⁻ z, ENNReal.ofReal (f z * weylFactor γ α z) ∂m0 := by
  have hstep : ∀ n : ℕ, ∫⁻ z, ENNReal.ofReal (f z * cutoff n z) ∂mα =
      ∫⁻ z, ENNReal.ofReal (f z * cutoff n z * weylFactor γ α z) ∂m0 := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hgc : Continuous (fun z => f z * cutoff n z) := hf.mul (continuous_cutoff n)
    have hgs : HasCompactSupport (fun z => f z * cutoff n z) := hfs.mul_right
    have hgδ : ∀ z : ℂ, ‖z‖ < 1 / ((n : ℝ) + 1) → f z * cutoff n z = 0 := by
      intro z hz
      have hz' : ((n : ℝ) + 1) * ‖z‖ < 1 := by
        have := (lt_div_iff₀ hpos).1 hz
        linarith
      rw [cutoff_eq_zero hz', mul_zero]
    have hint1 : Integrable (fun z => f z * cutoff n z) mα := hgc.integrable_of_hasCompactSupport hgs
    have hgw : Continuous (fun z => f z * cutoff n z * weylFactor γ α z) :=
      continuous_mul_weylFactor hgc hδ hgδ
    have hint2 : Integrable (fun z => f z * cutoff n z * weylFactor γ α z) m0 :=
      hgw.integrable_of_hasCompactSupport (hgs.mul_right)
    have key := integral_test_eq hcomp hgm hhm hg_lim hh_lim hgc hgs hδ hgδ
    have hnn1 : 0 ≤ᵐ[mα] (fun z => f z * cutoff n z) :=
      Eventually.of_forall fun z => mul_nonneg (hf0 z) (cutoff_nonneg n z)
    have hnn2 : 0 ≤ᵐ[m0] (fun z => f z * cutoff n z * weylFactor γ α z) :=
      Eventually.of_forall fun z => mul_nonneg (mul_nonneg (hf0 z) (cutoff_nonneg n z)) (weylFactor_pos γ α z).le
    calc ∫⁻ z, ENNReal.ofReal (f z * cutoff n z) ∂mα
        = ENNReal.ofReal (∫ z, f z * cutoff n z ∂mα) := (ofReal_integral_eq_lintegral_ofReal hint1 hnn1).symm
      _ = ENNReal.ofReal (∫ z, f z * cutoff n z * weylFactor γ α z ∂m0) := by rw [key]
      _ = ∫⁻ z, ENNReal.ofReal (f z * cutoff n z * weylFactor γ α z) ∂m0 :=
          ofReal_integral_eq_lintegral_ofReal hint2 hnn2
  have hL : Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (f z * cutoff n z) ∂mα) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (f z) ∂mα)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) (Eventually.of_forall fun z => ?_) ?_
    · exact (ENNReal.measurable_ofReal.comp ((hf.mul (continuous_cutoff n)).measurable)).aemeasurable
    · intro n m hnm
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (cutoff_mono z hnm) (hf0 z))
    · filter_upwards [compl_mem_ae_iff.2 h0h] with z hz
      have hz' : z ≠ 0 := mem_compl_singleton_iff.1 hz
      have ht : Tendsto (fun n : ℕ => f z * cutoff n z) atTop (𝓝 (f z * 1)) :=
        (tendsto_cutoff hz').const_mul (f z)
      rw [mul_one] at ht
      exact (ENNReal.continuous_ofReal.tendsto (f z)).comp ht
  have hR : Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (f z * cutoff n z * weylFactor γ α z) ∂m0) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (f z * weylFactor γ α z) ∂m0)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) (Eventually.of_forall fun z => ?_) ?_
    · exact (ENNReal.measurable_ofReal.comp
        (((hf.mul (continuous_cutoff n)).measurable).mul (weylFactor_measurable γ α))).aemeasurable
    · intro n m hnm
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cutoff_mono z hnm) (hf0 z))
          (weylFactor_pos γ α z).le)
    · filter_upwards [compl_mem_ae_iff.2 h0g] with z hz
      have hz' : z ≠ 0 := mem_compl_singleton_iff.1 hz
      have ht : Tendsto (fun n : ℕ => f z * cutoff n z * weylFactor γ α z) atTop
          (𝓝 (f z * 1 * weylFactor γ α z)) :=
        ((tendsto_cutoff hz').const_mul (f z)).mul_const (weylFactor γ α z)
      rw [mul_one] at ht
      exact (ENNReal.continuous_ofReal.tendsto _).comp ht
  have hfun : (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (f z * cutoff n z) ∂mα) =
      (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (f z * cutoff n z * weylFactor γ α z) ∂m0) :=
    funext hstep
  rw [hfun] at hL
  exact tendsto_nhds_unique hL hR

/-- Nonnegative case in Bochner form. -/
lemma integral_eq_of_nonneg {γ α : ℝ} {hg hh : ℝ → ℂ → ℝ} {m0 mα : Measure ℂ}
    [IsLocallyFiniteMeasure m0] [IsLocallyFiniteMeasure mα]
    (hcomp : ∀ r z, 0 < r → r < ‖z‖ → hh r z = hg r z - α * Real.log ‖z‖)
    (hgm : ∀ k : ℕ, Measurable (hg (dyadicScale k)))
    (hhm : ∀ k : ℕ, Measurable (hh (dyadicScale k)))
    (hg_lim : IsLQGLimit γ hg m0) (hh_lim : IsLQGLimit γ hh mα)
    (h0g : m0 {0} = 0) (h0h : mα {0} = 0)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : ∀ z, 0 ≤ f z) :
    ∫ z, f z ∂mα = ∫ z, f z * weylFactor γ α z ∂m0 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun z => mul_nonneg (hf0 z) (weylFactor_pos γ α z).le)
      (hf.aestronglyMeasurable.mul (weylFactor_measurable γ α).aestronglyMeasurable),
    lintegral_eq_of_nonneg hcomp hgm hhm hg_lim hh_lim h0g h0h hf hfs hf0]

/-- General case: `∫ f dμ_α = ∫ f w dμ_0` for every continuous compactly supported `f`. -/
lemma integral_eq_general {γ α : ℝ} {hg hh : ℝ → ℂ → ℝ} {m0 mα : Measure ℂ}
    [IsLocallyFiniteMeasure m0] [IsLocallyFiniteMeasure mα]
    (hcomp : ∀ r z, 0 < r → r < ‖z‖ → hh r z = hg r z - α * Real.log ‖z‖)
    (hgm : ∀ k : ℕ, Measurable (hg (dyadicScale k)))
    (hhm : ∀ k : ℕ, Measurable (hh (dyadicScale k)))
    (hg_lim : IsLQGLimit γ hg m0) (hh_lim : IsLQGLimit γ hh mα)
    (h0g : m0 {0} = 0) (h0h : mα {0} = 0)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    ∫ z, f z ∂mα = ∫ z, f z * weylFactor γ α z ∂m0 := by
  have hp : Continuous (fun z => max (f z) 0) := hf.max continuous_const
  have hn : Continuous (fun z => max (-f z) 0) := hf.neg.max continuous_const
  have hps : HasCompactSupport (fun z => max (f z) 0) :=
    hasCompactSupport_of_zeros hfs fun z h => by simp [h]
  have hns : HasCompactSupport (fun z => max (-f z) 0) :=
    hasCompactSupport_of_zeros hfs fun z h => by simp [h]
  have hp0 : ∀ z, 0 ≤ max (f z) 0 := fun z => le_max_right _ _
  have hn0 : ∀ z, 0 ≤ max (-f z) 0 := fun z => le_max_right _ _
  have hid_p := integral_eq_of_nonneg hcomp hgm hhm hg_lim hh_lim h0g h0h hp hps hp0
  have hid_n := integral_eq_of_nonneg hcomp hgm hhm hg_lim hh_lim h0g h0h hn hns hn0
  have hsplit : ∀ z, f z = max (f z) 0 - max (-f z) 0 := by
    intro z
    rcases le_total (f z) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -f z)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith : -f z ≤ 0)]
      ring
  have hsplitw : ∀ z, f z * weylFactor γ α z =
      max (f z) 0 * weylFactor γ α z - max (-f z) 0 * weylFactor γ α z := by
    intro z
    rw [← sub_mul, ← hsplit z]
  have hint_p : Integrable (fun z => max (f z) 0) mα := hp.integrable_of_hasCompactSupport hps
  have hint_n : Integrable (fun z => max (-f z) 0) mα := hn.integrable_of_hasCompactSupport hns
  have hwp : Integrable (fun z => max (f z) 0 * weylFactor γ α z) m0 := by
    refine integrable_of_lintegral_ofReal ((hp.measurable).mul (weylFactor_measurable γ α))
      (fun z => mul_nonneg (hp0 z) (weylFactor_pos γ α z).le) ?_
    rw [← lintegral_eq_of_nonneg hcomp hgm hhm hg_lim hh_lim h0g h0h hp hps hp0]
    exact lintegral_ofReal_ne_top_of_integrable hint_p hp0
  have hwn : Integrable (fun z => max (-f z) 0 * weylFactor γ α z) m0 := by
    refine integrable_of_lintegral_ofReal ((hn.measurable).mul (weylFactor_measurable γ α))
      (fun z => mul_nonneg (hn0 z) (weylFactor_pos γ α z).le) ?_
    rw [← lintegral_eq_of_nonneg hcomp hgm hhm hg_lim hh_lim h0g h0h hn hns hn0]
    exact lintegral_ofReal_ne_top_of_integrable hint_n hn0
  calc ∫ z, f z ∂mα = ∫ z, (max (f z) 0 - max (-f z) 0) ∂mα := integral_congr_ae (Eventually.of_forall hsplit)
    _ = ∫ z, max (f z) 0 ∂mα - ∫ z, max (-f z) 0 ∂mα := integral_sub hint_p hint_n
    _ = ∫ z, max (f z) 0 * weylFactor γ α z ∂m0 - ∫ z, max (-f z) 0 * weylFactor γ α z ∂m0 := by
        rw [hid_p, hid_n]
    _ = ∫ z, (max (f z) 0 * weylFactor γ α z - max (-f z) 0 * weylFactor γ α z) ∂m0 :=
        (integral_sub hwp hwn).symm
    _ = ∫ z, f z * weylFactor γ α z ∂m0 := integral_congr_ae (Eventually.of_forall fun z => (hsplitw z).symm)

/-- **Singular Weyl change of measure (deterministic form).** If the approximations of `μ_0` (insertion
parameter `0`, circle averages `hg`) and of `μ_α` (circle averages `hh = hg - α log|·|`) converge vaguely, and
neither measure has an atom at `0`, then `μ_α = w · μ_0` as measures on `ℂ`, where `w(z) = |z|^{-γα}`.
Write-up Step 12, identity (1). -/
theorem measure_eq_weyl {γ α : ℝ} {hg hh : ℝ → ℂ → ℝ} {m0 mα : Measure ℂ}
    (hcomp : ∀ r z, 0 < r → r < ‖z‖ → hh r z = hg r z - α * Real.log ‖z‖)
    (hgm : ∀ k : ℕ, Measurable (hg (dyadicScale k)))
    (hhm : ∀ k : ℕ, Measurable (hh (dyadicScale k)))
    (hg_lim : IsLQGLimit γ hg m0) (hh_lim : IsLQGLimit γ hh mα)
    (h0g : m0 {0} = 0) (h0h : mα {0} = 0) :
    mα = m0.withDensity (fun z => ENNReal.ofReal (weylFactor γ α z)) := by
  have := hg_lim.isLocallyFiniteMeasure
  have := hh_lim.isLocallyFiniteMeasure
  have hwm : Measurable (fun z => ENNReal.ofReal (weylFactor γ α z)) :=
    ENNReal.measurable_ofReal.comp (weylFactor_measurable γ α)
  have hfin : IsLocallyFiniteMeasure (m0.withDensity fun z => ENNReal.ofReal (weylFactor γ α z)) := by
    refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩⟩
    rw [withDensity_apply _ measurableSet_ball]
    calc ∫⁻ z in ball x 1, ENNReal.ofReal (weylFactor γ α z) ∂m0
        ≤ ∫⁻ z in ball x 1, ENNReal.ofReal (bumpBall x z * weylFactor γ α z) ∂m0 := by
          apply setLIntegral_mono' measurableSet_ball
          intro z hz
          rw [bumpBall_one (mem_ball.1 hz).le, one_mul]
      _ ≤ ∫⁻ z, ENNReal.ofReal (bumpBall x z * weylFactor γ α z) ∂m0 := setLIntegral_le_lintegral _ _
      _ = ∫⁻ z, ENNReal.ofReal (bumpBall x z) ∂mα :=
          (lintegral_eq_of_nonneg hcomp hgm hhm hg_lim hh_lim h0g h0h (continuous_bumpBall x)
            (hasCompactSupport_bumpBall x) (bumpBall_nonneg x)).symm
      _ < ⊤ := lt_top_iff_ne_top.2 (lintegral_ofReal_ne_top_of_integrable
            ((continuous_bumpBall x).integrable_of_hasCompactSupport (hasCompactSupport_bumpBall x))
            (bumpBall_nonneg x))
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  refine (integral_eq_general hcomp hgm hhm hg_lim hh_lim h0g h0h f.continuous f.hasCompactSupport).trans ?_
  rw [integral_withDensity_eq_integral_toReal_smul hwm (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (weylFactor_pos γ α z).le]
  exact mul_comm _ _

/-- **Singular Weyl change of measure, almost surely (write-up Step 12, identity (1)).** For `0 < γ < 2`,
`α < Q_γ`, almost surely `μ_α = |z|^{-γα} μ_0` on `ℂ` (the same conull event for all of `ℂ`).
Inputs: the two nonatomicity statements (HB Fact 2.1 I, p. 9; `LQGMeasureNonatomic`, pending source-check) and
the frozen measurability `CircleAverageVersionMeasurableStmt`. -/
theorem singular_weyl_measure_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hN0 : LQGMeasureNonatomic P γ 0 hC hcirc) (hNα : LQGMeasureNonatomic P γ α hC hcirc)
    (hMeas : CircleAverageVersionMeasurableStmt P hcirc)
    {μ0 μα : Ω → Measure ℂ} (h0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hαμ : IsLQGMeasureOfField P γ α hcirc μα) :
    ∀ᵐ ω ∂P, μα ω = (μ0 ω).withDensity (fun z => ENNReal.ofReal (weylFactor γ α z)) := by
  have hq : 0 < lqgQ γ := by
    unfold lqgQ
    positivity
  have hn0 := hN0 hGFF hγ hγ2 hq μ0 h0
  have hnα := hNα hGFF hγ hγ2 hα μα hαμ
  have h0' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ0 ω) := h0
  have hαμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μα ω) := hαμ
  filter_upwards [h0', hαμ', hn0, hnα, hMeas] with ω hω0 hωα hn0ω hnαω hmω
  have hgm : ∀ k : ℕ, Measurable (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) := fun k =>
    measurable_fieldCircleAverage (dyadicScale_pos k) (hmω k)
  have hhm : ∀ k : ℕ, Measurable (fieldCircleAverage α (hcirc ω) (dyadicScale k)) := fun k =>
    measurable_fieldCircleAverage (dyadicScale_pos k) (hmω k)
  have hcomp : ∀ r z, 0 < r → r < ‖z‖ →
      fieldCircleAverage α (hcirc ω) r z = fieldCircleAverage 0 (hcirc ω) r z - α * Real.log ‖z‖ :=
    fun r z hr hrz => fieldCircleAverage_eq_sub hr hrz
  exact measure_eq_weyl hcomp hgm hhm hω0 hωα (hn0ω 0) (hnαω 0)

/-- **Mutual absolute continuity (write-up Step 12, identity (2)).** On the same almost-sure event, `μ_α ≪ μ_0`
and `μ_0 ≪ μ_α`, so the two measures have the same null sets. -/
theorem singular_weyl_absCont_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hN0 : LQGMeasureNonatomic P γ 0 hC hcirc) (hNα : LQGMeasureNonatomic P γ α hC hcirc)
    (hMeas : CircleAverageVersionMeasurableStmt P hcirc)
    {μ0 μα : Ω → Measure ℂ} (h0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hαμ : IsLQGMeasureOfField P γ α hcirc μα) :
    ∀ᵐ ω ∂P, μα ω ≪ μ0 ω ∧ μ0 ω ≪ μα ω := by
  filter_upwards [singular_weyl_measure_ae P hGFF hγ hγ2 hα hN0 hNα hMeas h0 hαμ] with ω hω
  rw [hω]
  refine ⟨withDensity_absolutelyContinuous _ _, withDensity_absolutelyContinuous' ?_ ?_⟩
  · exact (ENNReal.measurable_ofReal.comp (weylFactor_measurable γ α)).aemeasurable
  · exact Eventually.of_forall fun z => (ENNReal.ofReal_pos.2 (weylFactor_pos γ α z)).ne'

end HarmonicBalls.SingularWeyl

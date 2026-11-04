import HarmonicBalls.Proofs.Sec8.PotentialCutoffEnergy

/-! # Smooth logarithmic cutoffs near a planar point

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

open MeasureTheory Metric Set Filter
open scoped Topology ContDiff

namespace HarmonicBalls

/-- A smooth transition from zero on the disk of radius `exp (-2t)` to one
outside the disk of radius `exp (-t)`. -/
noncomputable def logarithmicInnerCutoff (t : ℝ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else Real.smoothTransition ((Real.log ‖z‖ + 2 * t) / t)

/-- The derivative of the smooth transition profile is uniformly bounded. -/
theorem exists_bound_fderiv_smoothTransition :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖fderiv ℝ Real.smoothTransition x‖ ≤ C := by
  have hc : Continuous (fderiv ℝ Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0 : ℝ) 1)
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hC x hx).trans (le_max_left _ _)
  · have hx' : x < 0 ∨ 1 < x := by simpa only [mem_Icc, not_and_or, not_le] using hx
    have hzero : fderiv ℝ Real.smoothTransition x = 0 := by
      rcases hx' with hx' | hx'
      · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
          filter_upwards [eventually_lt_nhds hx'] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        rw [heq.fderiv_eq]
        exact fderiv_const_apply _
      · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
          filter_upwards [eventually_gt_nhds hx'] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        rw [heq.fderiv_eq]
        exact fderiv_const_apply _
    rw [hzero, norm_zero]
    exact le_max_right _ _

/-- The logarithmic inner cutoff vanishes on its inner disk. -/
theorem logarithmicInnerCutoff_eq_zero {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-2 * t)) : logarithmicInnerCutoff t z = 0 := by
  by_cases hz0 : z = 0
  · simp [logarithmicInnerCutoff, hz0]
  · rw [logarithmicInnerCutoff, ite_eq_right hz0, Real.smoothTransition.zero_iff_nonpos]
    have hl : Real.log ‖z‖ ≤ -2 * t := by
      have h := Real.log_le_log (norm_pos_iff.mpr hz0) hz
      simpa only [Real.log_exp] using h
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) ht.le

/-- The logarithmic inner cutoff is one outside its outer disk. -/
theorem logarithmicInnerCutoff_eq_one {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : Real.exp (-t) ≤ ‖z‖) : logarithmicInnerCutoff t z = 1 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le hz)
  rw [logarithmicInnerCutoff, ite_eq_right hz0]
  apply Real.smoothTransition.one_of_one_le
  have hl : -t ≤ Real.log ‖z‖ := by
    have h := Real.log_le_log (Real.exp_pos (-t)) hz
    simpa only [Real.log_exp] using h
  rw [le_div_iff₀ ht]
  linarith

/-- The derivative of the cutoff vanishes strictly inside its inner disk. -/
theorem fderiv_logarithmicInnerCutoff_eq_zero_of_inner {t : ℝ} (ht : 0 < t)
    {z : ℂ} (hz : ‖z‖ < Real.exp (-2 * t)) :
    fderiv ℝ (logarithmicInnerCutoff t) z = 0 := by
  have heq : logarithmicInnerCutoff t =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℝ)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (eventually_lt_nhds hz)] with w hw
    exact logarithmicInnerCutoff_eq_zero ht hw.le
  rw [heq.fderiv_eq]
  exact fderiv_const_apply _

/-- The derivative of the cutoff vanishes strictly outside its outer disk. -/
theorem fderiv_logarithmicInnerCutoff_eq_zero_of_outer {t : ℝ} (ht : 0 < t)
    {z : ℂ} (hz : Real.exp (-t) < ‖z‖) :
    fderiv ℝ (logarithmicInnerCutoff t) z = 0 := by
  have heq : logarithmicInnerCutoff t =ᶠ[𝓝 z] (fun _ : ℂ => (1 : ℝ)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (eventually_gt_nhds hz)] with w hw
    exact logarithmicInnerCutoff_eq_one ht hw.le
  rw [heq.fderiv_eq]
  exact fderiv_const_apply _

/-- The logarithmic inner cutoff takes values in the unit interval. -/
theorem logarithmicInnerCutoff_mem_Icc (t : ℝ) (z : ℂ) :
    logarithmicInnerCutoff t z ∈ Icc (0 : ℝ) 1 := by
  by_cases hz : z = 0
  · simp [logarithmicInnerCutoff, hz]
  · simp only [logarithmicInnerCutoff, ite_eq_right hz, mem_Icc]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Despite the logarithmic formula, the cutoff is smooth at the origin,
because it vanishes on an open neighborhood there. -/
theorem contDiff_logarithmicInnerCutoff {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (logarithmicInnerCutoff t) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℂ => (0 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * t))] with y hy
    have hy' : ‖y‖ ≤ Real.exp (-2 * t) := by
      exact (mem_ball_zero_iff.mp hy).le
    exact logarithmicInnerCutoff_eq_zero ht hy'
  · have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
    have hlog : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖) z :=
      hn.log (norm_ne_zero_iff.mpr hz)
    have hprofile : ContDiffAt ℝ ∞
        (fun w : ℂ => Real.smoothTransition ((Real.log ‖w‖ + 2 * t) / t)) z :=
      Real.smoothTransition.contDiffAt.comp z ((hlog.add contDiffAt_const).div_const t)
    apply hprofile.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp only [logarithmicInnerCutoff, ite_eq_right hw]

/-- The derivative of the logarithmic radius has the expected inverse-radius
operator norm away from the origin. -/
theorem norm_fderiv_log_norm {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (fun w : ℂ => Real.log ‖w‖) z‖ = ‖z‖⁻¹ := by
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (contDiffAt_norm ℝ hz (n := 1)).differentiableAt (by norm_num)
  rw [fderiv.log hn (norm_ne_zero_iff.mpr hz), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), norm_fderiv_norm hn,
    mul_one]

/-- The inner cutoff gradient is bounded by `C / (t * ‖z‖)` away from the
origin, for any uniform derivative bound `C` on the transition profile. -/
theorem norm_fderiv_logarithmicInnerCutoff_le {t C : ℝ} (ht : 0 < t)
    (hC : ∀ x : ℝ, ‖fderiv ℝ Real.smoothTransition x‖ ≤ C) {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (logarithmicInnerCutoff t) z‖ ≤ C / (t * ‖z‖) := by
  let a : ℂ → ℝ := fun w => t⁻¹ * (Real.log ‖w‖ + 2 * t)
  have hn : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
    (contDiffAt_norm ℝ hz (n := 1)).differentiableAt (by norm_num)
  have hl : DifferentiableAt ℝ (fun w : ℂ => Real.log ‖w‖) z :=
    hn.log (norm_ne_zero_iff.mpr hz)
  have ha : DifferentiableAt ℝ a z := by
    dsimp only [a]
    exact (hl.add_const (2 * t)).const_mul t⁻¹
  have hf : DifferentiableAt ℝ Real.smoothTransition (a z) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _
  have heq : logarithmicInnerCutoff t =ᶠ[𝓝 z] (Real.smoothTransition ∘ a) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp only [logarithmicInnerCutoff, ite_eq_right hw, Function.comp_apply, a, div_eq_mul_inv, mul_comm]
  have haeq : fderiv ℝ a z = t⁻¹ • fderiv ℝ (fun w : ℂ => Real.log ‖w‖) z := by
    dsimp only [a]
    rw [fderiv_const_mul (hl.add_const _) _, fderiv_add_const]
  rw [heq.fderiv_eq, fderiv_comp z hf ha]
  calc
    _ ≤ ‖fderiv ℝ Real.smoothTransition (a z)‖ * ‖fderiv ℝ a z‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * (t⁻¹ * ‖z‖⁻¹) := by
      rw [haeq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht.le),
        norm_fderiv_log_norm hz]
      exact mul_le_mul_of_nonneg_right (hC _) (mul_nonneg (inv_nonneg.mpr ht.le)
        (inv_nonneg.mpr (norm_nonneg _)))
    _ = C / (t * ‖z‖) := by rw [div_eq_mul_inv, mul_inv_rev]; ring

/-- At every nonzero point the logarithmic cutoffs eventually equal one. -/
theorem eventually_logarithmicInnerCutoff_eq_one {z : ℂ} (hz : z ≠ 0) :
    ∀ᶠ n : ℕ in atTop, logarithmicInnerCutoff (n + 1 : ℝ) z = 1 := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hcast)
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  filter_upwards [hexp.eventually (eventually_lt_nhds hzpos)] with n hn
  exact logarithmicInnerCutoff_eq_one (by positivity) hn.le

/-- The origin has zero measure, so the logarithmic cutoffs converge almost
everywhere to one. -/
theorem ae_tendsto_logarithmicInnerCutoff_one :
    ∀ᵐ z : ℂ ∂volume, Tendsto (fun n : ℕ => logarithmicInnerCutoff (n + 1 : ℝ) z)
      atTop (𝓝 1) := by
  filter_upwards [ae_ne_complex (0 : ℂ)] with z hz
  have heq : (fun n : ℕ => logarithmicInnerCutoff (n + 1 : ℝ) z) =ᶠ[atTop]
      (fun _ : ℕ => (1 : ℝ)) := eventually_logarithmicInnerCutoff_eq_one hz
  exact tendsto_const_nhds.congr' heq.symm

/-- Inserting any fixed power of the inner cutoff into an integrable source
does not change its integral in the limit. -/
theorem tendsto_integral_mul_logarithmicInnerCutoff_pow {f : ℂ → ℝ}
    (hf : Integrable f) (m : ℕ) :
    Tendsto (fun n : ℕ => ∫ z, f z * logarithmicInnerCutoff (n + 1 : ℝ) z ^ m)
      atTop (𝓝 (∫ z, f z)) := by
  have hm : ∀ n : ℕ, AEStronglyMeasurable
      (fun z => f z * logarithmicInnerCutoff (n + 1 : ℝ) z ^ m) volume := by
    intro n
    exact hf.aestronglyMeasurable.mul
      (((contDiff_logarithmicInnerCutoff (show 0 < (n + 1 : ℝ) by positivity)).continuous
        ).pow m).aestronglyMeasurable
  have hb : ∀ n : ℕ, ∀ᵐ z : ℂ ∂volume,
      ‖f z * logarithmicInnerCutoff (n + 1 : ℝ) z ^ m‖ ≤ ‖f z‖ := by
    intro n
    filter_upwards with z
    have hz := logarithmicInnerCutoff_mem_Icc (n + 1 : ℝ) z
    have hp0 : 0 ≤ logarithmicInnerCutoff (n + 1 : ℝ) z ^ m := pow_nonneg hz.1 _
    have hp1 : logarithmicInnerCutoff (n + 1 : ℝ) z ^ m ≤ 1 := pow_le_one₀ hz.1 hz.2
    rw [norm_mul]
    simp only [Real.norm_eq_abs, abs_of_nonneg hp0]
    exact mul_le_of_le_one_right (abs_nonneg _) hp1
  have hlim : ∀ᵐ z : ℂ ∂volume,
      Tendsto (fun n : ℕ => f z * logarithmicInnerCutoff (n + 1 : ℝ) z ^ m)
        atTop (𝓝 (f z)) := by
    filter_upwards [ae_tendsto_logarithmicInnerCutoff_one] with z hz
    simpa only [one_pow, mul_one] using (tendsto_const_nhds.mul (hz.pow m))
  exact tendsto_integral_of_dominated_convergence (fun z => ‖f z‖) hm hf.norm hb hlim

end HarmonicBalls

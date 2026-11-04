import HarmonicBalls.Proofs.Sec8.WeightedInnerCutoffEnergy
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
/-! # Smooth cutoffs at infinity

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real ContDiff
namespace HarmonicBalls

/-- A fixed smooth bump equal to one on the unit disk and supported in the disk of radius two. -/
noncomputable def outerBump : ContDiffBump (0 : ℂ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- A rescaled smooth bump used to cut off at infinity. -/
noncomputable def outerCutoff (R : ℝ) (z : ℂ) : ℝ := outerBump (R⁻¹ • z)

theorem contDiff_outerCutoff (R : ℝ) : ContDiff ℝ ∞ (outerCutoff R) := by
  change ContDiff ℝ ∞ (outerBump ∘ fun z : ℂ => R⁻¹ • z)
  exact outerBump.contDiff.comp (contDiff_id.const_smul R⁻¹)

theorem hasCompactSupport_outerCutoff {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (outerCutoff R) := by
  exact outerBump.hasCompactSupport.comp_smul (inv_ne_zero hR)

theorem outerCutoff_eq_one {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    outerCutoff R z = 1 := by
  apply outerBump.one_of_mem_closedBall
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hR.le)]
  change R⁻¹ * ‖z‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]
  simpa using hz

theorem outerCutoff_mem_Icc (R : ℝ) (z : ℂ) : outerCutoff R z ∈ Icc (0 : ℝ) 1 :=
  ⟨outerBump.nonneg, outerBump.le_one⟩

theorem fderiv_outerCutoff (R : ℝ) (z : ℂ) :
    fderiv ℝ (outerCutoff R) z = R⁻¹ • fderiv ℝ outerBump (R⁻¹ • z) := by
  exact fderiv_comp_smul R⁻¹

theorem integral_outerCutoff_energy {R : ℝ} (hR : 0 < R) :
    (∫ z : ℂ, ‖fderiv ℝ (outerCutoff R) z‖ ^ 2) =
      ∫ z : ℂ, ‖fderiv ℝ outerBump z‖ ^ 2 := by
  have heq : (fun z : ℂ => ‖fderiv ℝ (outerCutoff R) z‖ ^ 2) =
      fun z : ℂ => (R⁻¹) ^ 2 * ‖fderiv ℝ outerBump (R⁻¹ • z)‖ ^ 2 := by
    funext z
    rw [fderiv_outerCutoff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
    ring
  rw [heq, integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun z : ℂ => ‖fderiv ℝ outerBump z‖ ^ 2) hR.le]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  field_simp
theorem fderiv_outerCutoff_eq_zero_of_inner {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : ‖z‖ < R) : fderiv ℝ (outerCutoff R) z = 0 := by
  have heq : outerCutoff R =ᶠ[𝓝 z] (fun _ : ℂ => (1 : ℝ)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (eventually_lt_nhds hz)] with w hw
    exact outerCutoff_eq_one hR hw.le
  rw [heq.fderiv_eq]
  exact fderiv_const_apply _

theorem integrable_outerCutoff_gradient_sq {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : ℂ => ‖fderiv ℝ (outerCutoff R) z‖ ^ 2) := by
  have hc : Continuous (fderiv ℝ (outerCutoff R)) :=
    (contDiff_outerCutoff R).continuous_fderiv (by norm_num)
  have hd : HasCompactSupport (fderiv ℝ (outerCutoff R)) :=
    (hasCompactSupport_outerCutoff hR.ne').fderiv (𝕜 := ℝ)
  exact (hc.norm.pow 2).integrable_of_hasCompactSupport (by
    simpa only [pow_two] using hd.norm.mul_right
      (f' := fun z => ‖fderiv ℝ (outerCutoff R) z‖))

theorem eventually_outerCutoff_eq_one (z : ℂ) :
    ∀ᶠ n : ℕ in atTop, outerCutoff (n + 1 : ℝ) z = 1 := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (eventually_ge_atTop ‖z‖)] with n hn
  exact outerCutoff_eq_one (by positivity) hn
end HarmonicBalls

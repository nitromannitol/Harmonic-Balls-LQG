import HarmonicBalls.Proofs.Sec8.LogarithmicPotential

/-! # Decay estimates for planar logarithmic potentials

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

open MeasureTheory Metric Set Laplacian Filter
open scoped Topology

namespace HarmonicBalls

/-- On the positive half-line, the logarithm has a quantitative modulus of
continuity on the interval whose left endpoint is half of `b`. -/
theorem abs_log_sub_le_of_half_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ 2 * a) :
    |Real.log a - Real.log b| ≤ 2 * |a - b| / b := by
  have hforward := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hforward
  have hbackward := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hbackward
  have hforward' : Real.log a - Real.log b ≤ (a - b) / b := by
    convert hforward using 1; field_simp
  have hbackward' : Real.log b - Real.log a ≤ (b - a) / a := by
    convert hbackward using 1; field_simp
  have hpos : 0 ≤ |a - b| := abs_nonneg _
  have hup : Real.log a - Real.log b ≤ 2 * |a - b| / b := by
    apply (le_div_iff₀ hb).2
    have h := (le_div_iff₀ hb).1 hforward'
    have hsub := le_abs_self (a - b)
    nlinarith
  have hdown : -(2 * |a - b| / b) ≤ Real.log a - Real.log b := by
    have hsub := neg_le_abs (a - b)
    have hratio : (b - a) / a ≤ 2 * |a - b| / b := by
      apply (div_le_div_iff₀ ha hb).2
      nlinarith
    linarith
  exact abs_le.mpr ⟨hdown, hup⟩

/-- Away from the support, the translated logarithmic kernel differs from
its value at the origin by at most a constant times `‖y‖ / ‖x‖`. -/
theorem abs_log_norm_sub_log_norm_le {x y : ℂ} (hx : x ≠ 0)
    (hxy : 2 * ‖y‖ ≤ ‖x‖) :
    |Real.log ‖y - x‖ - Real.log ‖x‖| ≤ 2 * ‖y‖ / ‖x‖ := by
  have hxb : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hdiff : |‖y - x‖ - ‖x‖| ≤ ‖y‖ := by
    simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using abs_norm_sub_norm_le (y - x) (-x)
  have hbound : ‖x‖ ≤ 2 * ‖y - x‖ := by
    have h := neg_le_abs (‖y - x‖ - ‖x‖)
    linarith
  have hya : 0 < ‖y - x‖ := by linarith
  exact (abs_log_sub_le_of_half_le hya hxb hbound).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num)) hxb.le)

/-- Cancellation of total mass removes the logarithmic growth of the planar
potential's kernel. -/
theorem planarLogPotential_eq_integral_log_difference {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφzero : ∫ y, φ y = 0)
    (x : ℂ) :
    planarLogPotential φ x = (2 * Real.pi)⁻¹ *
      ∫ y, φ y * (Real.log ‖y - x‖ - Real.log ‖x‖) := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hli : Integrable (fun y => φ y * Real.log ‖y - x‖) := by
    have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
      ).integrable_smul_right_of_hasCompactSupport hφ hφc
    simpa only [smul_eq_mul, mul_comm] using h
  rw [planarLogPotential_eq_integral]
  congr 1
  calc
    _ = (∫ y, φ y * Real.log ‖y - x‖) - ∫ y, φ y * Real.log ‖x‖ := by
      rw [integral_mul_const, hφzero, zero_mul, sub_zero]
    _ = ∫ y, φ y * Real.log ‖y - x‖ - φ y * Real.log ‖x‖ := by
      rw [integral_sub hli (hφi.mul_const _)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      ring

/-- A compactly supported mean-zero density has a logarithmic potential with
an explicit inverse-distance bound outside twice its support radius. -/
theorem abs_planarLogPotential_le_of_support_radius {φ : ℂ → ℝ} {R : ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφzero : ∫ y, φ y = 0)
    (hsupp : ∀ y, φ y ≠ 0 → ‖y‖ ≤ R)
    {x : ℂ} (hx : x ≠ 0) (hfar : 2 * R ≤ ‖x‖) :
    |planarLogPotential φ x| ≤ (2 * Real.pi)⁻¹ *
      ((∫ y, ‖φ y‖) * (2 * R / ‖x‖)) := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hxi : 0 ≤ ‖x‖ := norm_nonneg _
  have hbnd : ∀ y : ℂ,
      ‖φ y * (Real.log ‖y - x‖ - Real.log ‖x‖)‖ ≤
        ‖φ y‖ * (2 * R / ‖x‖) := by
    intro y
    by_cases hy : φ y = 0
    · simp [hy]
    · have hyr := hsupp y hy
      have hyx : 2 * ‖y‖ ≤ ‖x‖ := by nlinarith
      have hl := abs_log_norm_sub_log_norm_le hx hyx
      have hl' : |Real.log ‖y - x‖ - Real.log ‖x‖| ≤ 2 * R / ‖x‖ :=
        hl.trans (div_le_div_of_nonneg_right (by nlinarith) hxi)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hl' (abs_nonneg _)
  have hi : Integrable (fun y : ℂ => ‖φ y‖ * (2 * R / ‖x‖)) :=
    hφi.norm.mul_const _
  have hmain := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hbnd)
  rw [integral_mul_const] at hmain
  rw [planarLogPotential_eq_integral_log_difference hφ hφc hφzero, abs_mul]
  rw [abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr (by positivity))

/-- The logarithmic potential of a compactly supported mean-zero density
vanishes at infinity. -/
theorem tendsto_planarLogPotential_cocompact {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφzero : ∫ y, φ y = 0) :
    Tendsto (planarLogPotential φ) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_closedBall (0 : ℂ)
  have hsupp : ∀ y, φ y ≠ 0 → ‖y‖ ≤ R := by
    intro y hy
    have hy' := hR (subset_tsupport φ (show y ∈ Function.support φ from hy))
    simpa only [mem_closedBall, dist_zero_right] using hy'
  have hnorm : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  have hbound : Tendsto (fun x : ℂ => (2 * Real.pi)⁻¹ *
      ((∫ y, ‖φ y‖) * (2 * R / ‖x‖))) (cocompact ℂ) (𝓝 0) := by
    have hinv : Tendsto (fun x : ℂ => ‖x‖⁻¹) (cocompact ℂ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hnorm
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := (2 * Real.pi)⁻¹)).mul
        ((tendsto_const_nhds (x := ∫ y, ‖φ y‖)).mul
          ((tendsto_const_nhds (x := 2 * R)).mul hinv))
  have hevent : ∀ᶠ x : ℂ in cocompact ℂ, x ≠ 0 ∧ 2 * R ≤ ‖x‖ := by
    filter_upwards [hnorm.eventually (eventually_ge_atTop (max (2 * R) 1))] with x hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hx)
    exact ⟨norm_pos_iff.mp hxpos, le_trans (le_max_left _ _) hx⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_ hbound
  filter_upwards [hevent] with x hx
  simpa only [Real.norm_eq_abs] using
    abs_planarLogPotential_le_of_support_radius hφ hφc hφzero hsupp hx.1 hx.2

end HarmonicBalls

import HarmonicBalls.Proofs.Sec8.LogarithmicCutoffPolar

/-! # Dirichlet energy of a logarithmic cutoff

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real ContDiff
namespace HarmonicBalls

theorem integrable_inverse_square_closed_annulus {a b : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ => (Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) := by
  let K : Set ℂ := {z | a ≤ ‖z‖ ∧ ‖z‖ ≤ b}
  let S : Set ℂ := {z | ‖z‖ ∈ Icc a b}
  have hKclosed : IsClosed K := (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset hKclosed (by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hz.2)
  have hSmeas : MeasurableSet S := measurableSet_Icc.preimage continuous_norm.measurable
  have hSK : S ⊆ K := by
    intro z hz
    exact ⟨hz.1, hz.2⟩
  have hc : ContinuousOn (fun z : ℂ => (‖z‖ ^ 2)⁻¹) K := by
    apply (continuous_norm.pow 2).continuousOn.inv₀
    intro z hz
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hz.1))
  have hi : IntegrableOn (fun z : ℂ => (‖z‖ ^ 2)⁻¹) S :=
    (hc.integrableOn_compact hK).mono_set hSK
  have hi' := hi.integrable_indicator hSmeas
  convert hi' using 1
  funext z
  by_cases hz : ‖z‖ ∈ Icc a b
  · have hs : z ∈ S := hz
    simp [hz, hs]
  · have hs : z ∉ S := hz
    simp [hz, hs]
theorem integral_inverse_square_closed_annulus {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ z : ℂ, (Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) =
      2 * Real.pi * Real.log (b / a) := by
  rw [show (∫ z : ℂ, (Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) =
      2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * (Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) r by
        simpa using integral_radial ((Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹)) 0]
  congr 1
  have heq : (fun r : ℝ => r * (Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) r) =
      (Icc a b).indicator (fun r : ℝ => r⁻¹) := by
    funext r
    by_cases hr : r ∈ Icc a b
    · have hne : r ≠ 0 := ne_of_gt (ha.trans_le hr.1)
      simp only [indicator_of_mem hr]
      field_simp
    · simp [indicator_of_notMem hr]
  rw [heq, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hint : Icc a b ∩ Ioi 0 = Icc a b := by
    ext r
    simp only [mem_inter_iff, mem_Icc, mem_Ioi]
    constructor
    · exact And.left
    · intro hr
      exact ⟨hr, ha.trans_le hr.1⟩
  rw [hint, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_inv_of_pos ha (ha.trans_le hab)]
theorem logarithmicInnerCutoff_gradient_sq_le {t C : ℝ} (ht : 0 < t) (hC0 : 0 ≤ C)
    (hC : ∀ x : ℝ, ‖fderiv ℝ Real.smoothTransition x‖ ≤ C) (z : ℂ) :
    ‖fderiv ℝ (logarithmicInnerCutoff t) z‖ ^ 2 ≤
      (C / t) ^ 2 * (Icc (Real.exp (-2 * t)) (Real.exp (-t))).indicator
        (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖ := by
  by_cases hz : ‖z‖ ∈ Icc (Real.exp (-2 * t)) (Real.exp (-t))
  · have hz0 : z ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le hz.1)
    have hb := norm_fderiv_logarithmicInnerCutoff_le ht hC hz0
    have hpos : 0 ≤ C / (t * ‖z‖) := div_nonneg hC0 (mul_nonneg ht.le (norm_nonneg _))
    rw [indicator_of_mem hz]
    calc
      _ ≤ (C / (t * ‖z‖)) ^ 2 := sq_le_sq₀ (norm_nonneg _) hpos |>.2 hb
      _ = (C / t) ^ 2 * (‖z‖ ^ 2)⁻¹ := by
        field_simp
  · have hz' : ‖z‖ < Real.exp (-2 * t) ∨ Real.exp (-t) < ‖z‖ := by
      simpa only [mem_Icc, not_and_or, not_le] using hz
    have hd : fderiv ℝ (logarithmicInnerCutoff t) z = 0 := by
      rcases hz' with hz' | hz'
      · exact fderiv_logarithmicInnerCutoff_eq_zero_of_inner ht hz'
      · exact fderiv_logarithmicInnerCutoff_eq_zero_of_outer ht hz'
    rw [indicator_of_notMem hz, hd]
    simp

/-- The squared gradient of the logarithmic cutoff is integrable. -/
theorem integrable_logarithmicInnerCutoff_gradient_sq {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hC : ∀ x : ℝ, ‖fderiv ℝ Real.smoothTransition x‖ ≤ C) :
    Integrable (fun z : ℂ => ‖fderiv ℝ (logarithmicInnerCutoff t) z‖ ^ 2) := by
  have hb : Integrable (fun z : ℂ => (C / t) ^ 2 *
      (Icc (Real.exp (-2 * t)) (Real.exp (-t))).indicator
        (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) :=
    (integrable_inverse_square_closed_annulus (Real.exp_pos _)).const_mul _
  have hc : Continuous (fderiv ℝ (logarithmicInnerCutoff t)) :=
    (contDiff_logarithmicInnerCutoff ht).continuous_fderiv (by norm_num)
  apply Integrable.mono' hb (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact logarithmicInnerCutoff_gradient_sq_le ht hC0 hC z

/-- The logarithmic inner cutoffs have Dirichlet energy at most order `1/t`. -/
theorem integral_logarithmicInnerCutoff_gradient_sq_le {t C : ℝ} (ht : 0 < t)
    (hC0 : 0 ≤ C) (hC : ∀ x : ℝ, ‖fderiv ℝ Real.smoothTransition x‖ ≤ C) :
    (∫ z : ℂ, ‖fderiv ℝ (logarithmicInnerCutoff t) z‖ ^ 2) ≤ 2 * Real.pi * C ^ 2 / t := by
  let a := Real.exp (-2 * t)
  let b := Real.exp (-t)
  have hab : a ≤ b := by dsimp [a, b]; apply Real.exp_le_exp.mpr; linarith
  have hbi : Integrable (fun z : ℂ => (C / t) ^ 2 *
      (Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖) :=
    (integrable_inverse_square_closed_annulus (Real.exp_pos (-2 * t))).const_mul _
  calc
    _ ≤ ∫ z : ℂ, (C / t) ^ 2 * (Icc a b).indicator (fun r : ℝ => (r ^ 2)⁻¹) ‖z‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) hbi
      exact Filter.Eventually.of_forall (logarithmicInnerCutoff_gradient_sq_le ht hC0 hC)
    _ = (C / t) ^ 2 * (2 * Real.pi * Real.log (b / a)) := by
      rw [integral_const_mul, integral_inverse_square_closed_annulus (Real.exp_pos _) hab]
    _ = 2 * Real.pi * C ^ 2 / t := by
      dsimp [a, b]
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)),
        Real.log_exp, Real.log_exp]
      field_simp
      ring
/-- The Dirichlet energies of the shrinking inner cutoffs tend to zero. -/
theorem tendsto_integral_logarithmicInnerCutoff_gradient_sq :
    Tendsto (fun n : ℕ => ∫ z : ℂ,
      ‖fderiv ℝ (logarithmicInnerCutoff (n + 1 : ℝ)) z‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_fderiv_smoothTransition
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => 2 * Real.pi * C ^ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  apply squeeze_zero (fun n => integral_nonneg fun z => sq_nonneg _) _ hlim
  intro n
  exact integral_logarithmicInnerCutoff_gradient_sq_le (by positivity) hC0 hC

end HarmonicBalls

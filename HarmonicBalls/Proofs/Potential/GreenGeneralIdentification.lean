import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-!
# Green potentials on a smooth bounded open set: the logarithmic potential

Part of the deterministic general-domain Green potential estimate `GreenPotentialGeneralStep`
(Proposition 2.5, Green clause), following the written argument steps4-final Section 1: the logarithmic
potential `V x = ∫ N(x,y) f(y) ν(dy)` of a bounded density against a measure with a uniform negative
moment `∫ ‖x - y‖^(-α) ν(dy) ≤ K` is absolutely convergent and `α`-Hölder (lines 80-124).

Here `N = newtonKernel` is the Newtonian kernel `-(2π)⁻¹ log ‖x - y‖` (Armitage–Gardiner §4.1).
-/

namespace HarmonicBalls

namespace GreenGeneral

open MeasureTheory Metric Set

/-- `|log t| ≤ α⁻¹ (t^(-α) + t^α)` for `t > 0` and `α > 0`. -/
theorem abs_log_le_rpow_neg_add_rpow {t α : ℝ} (ht : 0 < t) (hα : 0 < α) :
    |Real.log t| ≤ α⁻¹ * (t ^ (-α) + t ^ α) := by
  have h1 : Real.log t ≤ t ^ α / α := Real.log_le_rpow_div ht.le hα
  have h2 : Real.log t⁻¹ ≤ t⁻¹ ^ α / α := Real.log_le_rpow_div (inv_pos.2 ht).le hα
  rw [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at h2
  have hp : 0 ≤ t ^ α := Real.rpow_nonneg ht.le _
  have hn : 0 ≤ t ^ (-α) := Real.rpow_nonneg ht.le _
  rw [abs_le]
  constructor
  · have : t ^ (-α) / α ≤ α⁻¹ * (t ^ (-α) + t ^ α) := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hα.le)
    linarith
  · have : t ^ α / α ≤ α⁻¹ * (t ^ (-α) + t ^ α) := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hα.le)
    linarith

/-- Hölder difference bound for the Newtonian kernel in its first variable, off the two poles. -/
theorem abs_newtonKernel_sub_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {x x' y : ℂ}
    (hx : y ≠ x) (hx' : y ≠ x') :
    |newtonKernel x y - newtonKernel x' y| ≤
      (2 * Real.pi)⁻¹ * (α⁻¹ * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α)))) := by
  have ha : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hx))
  have hb : 0 < ‖x' - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hx'))
  have hlog := abs_log_sub_log_le ha hb hα hα1
  have hdiff : |‖x - y‖ - ‖x' - y‖| ^ α ≤ ‖x - x'‖ ^ α := by
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ hα.le
    have := abs_norm_sub_norm_le (x - y) (x' - y)
    simpa using this
  have hsum : 0 ≤ ‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α) :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  have hk : newtonKernel x y - newtonKernel x' y =
      -(2 * Real.pi)⁻¹ * (Real.log ‖x - y‖ - Real.log ‖x' - y‖) := by
    simp only [newtonKernel]; ring
  rw [hk, abs_mul, abs_neg, abs_of_nonneg hπ]
  refine mul_le_mul_of_nonneg_left (hlog.trans ?_) hπ
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdiff hsum) (inv_nonneg.2 hα.le)

/-- **The logarithmic potential of a bounded density** (steps4-final lines 80-124). Let `ν` be a finite measure
carried by `closedBall 0 R`, without atoms there, with the uniform negative moment
`∫ ‖x - y‖^(-α) ν(dy) ≤ K` for `x ∈ closedBall 0 R`, and let `|f| ≤ M` `ν`-a.e. Then
`y ↦ N(x,y) f(y)` is `ν`-integrable for every `x ∈ closedBall 0 R`, and the logarithmic potential is
`α`-Hölder there with constant `(π α)⁻¹ K M`. -/
theorem newtonPotential_integrable_and_sub_le {ν : Measure ℂ} [IsFiniteMeasure ν] {R α K M : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hK0 : 0 ≤ K) (hsupp : ∀ᵐ y ∂ν, ‖y‖ ≤ R)
    (hK : ∀ x ∈ closedBall (0 : ℂ) R, ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂ν ≤ ENNReal.ofReal K)
    (hatom : ∀ x ∈ closedBall (0 : ℂ) R, ν {x} = 0) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f ν)
    (hM : 0 ≤ M) (hfM : ∀ᵐ y ∂ν, |f y| ≤ M) :
    (∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => newtonKernel x y * f y) ν) ∧
    ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
      |∫ y, newtonKernel x y * f y ∂ν - ∫ y, newtonKernel x' y * f y ∂ν| ≤
        (Real.pi * α)⁻¹ * K * M * ‖x - x'‖ ^ α := by
  have hint := fun x hx => integrable_norm_sub_rpow_neg hK0 (hK x hx)
  have hne : ∀ x ∈ closedBall (0 : ℂ) R, ∀ᵐ y ∂ν, y ≠ x := fun x hx =>
    ae_iff.2 (by simpa using hatom x hx)
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  have hαi : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  have hmeasN : ∀ x, AEStronglyMeasurable (fun y => newtonKernel x y * f y) ν := by
    intro x
    have : Measurable fun y : ℂ => newtonKernel x y := by
      unfold newtonKernel; fun_prop
    exact this.aestronglyMeasurable.mul hf
  -- integrability: `|N(x,y)| ≤ (2π)⁻¹ α⁻¹ (‖x-y‖^(-α) + (2R)^α)` on the support
  have hI : ∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => newtonKernel x y * f y) ν := by
    intro x hx
    have hdom : Integrable (fun y => M * ((2 * Real.pi)⁻¹ *
        (α⁻¹ * (‖x - y‖ ^ (-α) + (2 * R) ^ α)))) ν :=
      ((((hint x hx).1.add (integrable_const _)).const_mul _).const_mul _).const_mul _
    refine hdom.mono' (hmeasN x) ?_
    filter_upwards [hne x hx, hsupp, hfM] with y hyx hyR hy
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hyx))
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 hx
    have hle : ‖x - y‖ ^ α ≤ (2 * R) ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) ((norm_sub_le x y).trans (by linarith)) hα.le
    have hlog := abs_log_le_rpow_neg_add_rpow hpos hα
    have hN : |newtonKernel x y| ≤ (2 * Real.pi)⁻¹ * (α⁻¹ * (‖x - y‖ ^ (-α) + (2 * R) ^ α)) := by
      rw [newtonKernel, abs_mul, abs_neg, abs_of_nonneg hπ]
      refine mul_le_mul_of_nonneg_left (hlog.trans ?_) hπ
      exact mul_le_mul_of_nonneg_left (by linarith) hαi
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul hy hN (abs_nonneg _) hM
  refine ⟨hI, fun x hx x' hx' => ?_⟩
  set c := (2 * Real.pi)⁻¹ * α⁻¹ with hc_def
  have hc : 0 ≤ c := mul_nonneg hπ hαi
  have hdom : Integrable (fun y => M * (c * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α))))) ν :=
    ((((hint x hx).1.add (hint x' hx').1).const_mul _).const_mul _).const_mul _
  rw [← integral_sub (hI x hx) (hI x' hx'), ← Real.norm_eq_abs]
  calc ‖∫ y, (newtonKernel x y * f y - newtonKernel x' y * f y) ∂ν‖
      ≤ ∫ y, M * (c * (‖x - x'‖ ^ α * (‖x - y‖ ^ (-α) + ‖x' - y‖ ^ (-α)))) ∂ν := by
        refine norm_integral_le_of_norm_le hdom ?_
        filter_upwards [hne x hx, hne x' hx', hfM] with y hyx hyx' hy
        rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm]
        refine mul_le_mul hy ?_ (abs_nonneg _) hM
        have := abs_newtonKernel_sub_le hα hα1 hyx hyx'
        rw [hc_def, mul_assoc]
        exact this
    _ = M * (c * (‖x - x'‖ ^ α * (∫ y, ‖x - y‖ ^ (-α) ∂ν + ∫ y, ‖x' - y‖ ^ (-α) ∂ν))) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          integral_add (hint x hx).1 (hint x' hx').1]
    _ ≤ M * (c * (‖x - x'‖ ^ α * (K + K))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add (hint x hx).2 (hint x' hx').2) (Real.rpow_nonneg (norm_nonneg _) _)) hc) hM
    _ = (Real.pi * α)⁻¹ * K * M * ‖x - x'‖ ^ α := by
        rw [hc_def, mul_inv, mul_inv]; ring

end GreenGeneral

end HarmonicBalls

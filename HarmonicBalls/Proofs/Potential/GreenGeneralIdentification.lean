import HarmonicBalls.Proofs.Potential.GreenPotentialHolder
import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity

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

/-- `log⁺ s ≤ α⁻¹ s^α` for `s ≥ 0` and `α > 0`. -/
theorem posLog_le_inv_mul_rpow {s α : ℝ} (hs : 0 ≤ s) (hα : 0 < α) :
    Real.posLog s ≤ α⁻¹ * s ^ α := by
  rw [Real.posLog_def, Pi.sup_apply, Pi.zero_apply, sup_le_iff]
  refine ⟨mul_nonneg (inv_nonneg.2 hα.le) (Real.rpow_nonneg hs _), ?_⟩
  rw [inv_mul_eq_div]
  exact Real.log_le_rpow_div hs hα

/-- **Uniform negative moment under upper volume growth** (blueprint G1). If `μ` has the volume growth of
exponents `β⁻, β⁺` on `B_R` and `O ⊆ B_R`, then `ν = μ|_O` has no atoms in `closedBall 0 R` and
`∫ ‖x - y‖^(-α) ν(dy) ≤ K` uniformly in `x ∈ closedBall 0 R`, with `α = greenPotentialHolderExponent β⁺`. -/
theorem VolumeGrowth.negMoment_restrict {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R βminus βplus : ℝ}
    (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) {O : Set ℂ} (hO : O ⊆ ball (0 : ℂ) R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ closedBall (0 : ℂ) R,
      ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-greenPotentialHolderExponent βplus)) ∂(μ.restrict O) ≤
        ENNReal.ofReal K ∧ μ.restrict O {x} = 0 := by
  obtain ⟨-, hβ, r₀, hr₀, hgr⟩ := hμ
  have hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus) :=
    fun r hr hrr z hz => (hgr r hr hrr z hz).2
  have hfin : μ (ball (0 : ℂ) R) ≠ ⊤ := measure_ball_lt_top.ne
  set m := (μ (ball (0 : ℂ) R)).toReal with hm_def
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hα := greenPotentialHolderExponent_pos hβ
  have hball := fun x (hx : x ∈ closedBall (0 : ℂ) R) r (hr : 0 < r) =>
    restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr
  have hν : μ.restrict (ball 0 R) univ ≤ ENNReal.ofReal m := by
    rw [Measure.restrict_apply_univ, hm_def, ENNReal.ofReal_toReal hfin]
  have hle : μ.restrict O ≤ μ.restrict (ball 0 R) := Measure.restrict_mono hO le_rfl
  refine ⟨greenPotentialRieszBound βplus r₀ m, greenPotentialRieszBound_nonneg hβ hr₀ hm,
    fun x hx => ⟨?_, ?_⟩⟩
  · exact (lintegral_mono' hle le_rfl).trans (lintegral_norm_sub_rpow_neg_le hα
      (greenPotentialHolderExponent_lt hβ) hm (volumeGrowthAllScalesConstant_nonneg hr₀ hm) hν (hball x hx))
  · exact nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hle {x}).trans
      (measure_singleton_eq_zero_of_le_rpow hβ (hball x hx)).le)

/-- `μ|_O` is finite when `O` lies in a ball and `μ` is locally finite. -/
theorem isFiniteMeasure_restrict_of_subset_ball {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R : ℝ}
    {O : Set ℂ} (hO : O ⊆ ball (0 : ℂ) R) : IsFiniteMeasure (μ.restrict O) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hO).trans_lt measure_ball_lt_top⟩

/-- **The logarithmic potential under the volume growth condition** (blueprint G1 + G2). For `O ⊆ B_R`
measurable, the logarithmic potential `x ↦ ∫_O N(x,y) f(y) μ(dy)` of a density with `|f| ≤ M` `μ`-a.e. on `O`
converges absolutely on `closedBall 0 R` and is Hölder there with exponent `min(β⁺,1)/2` and constant `C M`,
`C` independent of `f`. -/
theorem VolumeGrowth.newtonPotential_holder {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R βminus βplus : ℝ} (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) {O : Set ℂ}
    (hOm : MeasurableSet O) (hO : O ⊆ ball (0 : ℂ) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℝ) (M : ℝ), AEStronglyMeasurable f (μ.restrict O) → 0 ≤ M →
      (∀ᵐ y ∂μ.restrict O, |f y| ≤ M) →
      (∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => newtonKernel x y * f y) (μ.restrict O)) ∧
      ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
        |∫ y, newtonKernel x y * f y ∂(μ.restrict O) - ∫ y, newtonKernel x' y * f y ∂(μ.restrict O)| ≤
          C * M * ‖x - x'‖ ^ greenPotentialHolderExponent βplus := by
  have hβ : 0 < βplus := hμ.2.1
  obtain ⟨K, hK0, hK⟩ := VolumeGrowth.negMoment_restrict hR hμ hO
  have := isFiniteMeasure_restrict_of_subset_ball (μ := μ) hO
  have hα := greenPotentialHolderExponent_pos hβ
  have hsupp : ∀ᵐ y ∂μ.restrict O, ‖y‖ ≤ R :=
    (ae_restrict_iff' hOm).2 (Filter.Eventually.of_forall fun y hy => (mem_ball_zero_iff.1 (hO hy)).le)
  refine ⟨(Real.pi * greenPotentialHolderExponent βplus)⁻¹ * K,
    mul_nonneg (inv_nonneg.2 (mul_nonneg Real.pi_pos.le hα.le)) hK0, fun f M hf hM hfM => ?_⟩
  exact newtonPotential_integrable_and_sub_le hα (greenPotentialHolderExponent_le_one βplus) hK0 hsupp
    (fun x hx => (hK x hx).1) (fun x hx => (hK x hx).2) hf hM hfM

/-- **Absolute convergence of the Green potential** (blueprint G3; first conjunct of the general-domain step).
For `O ⊆ B_R` open and `μ` with the volume growth condition on `B_R`, `y ↦ G_O(x,y) f(y)` is `μ`-integrable on
`O` for every `x ∈ closedBall 0 R` and every density with `|f| ≤ M` `μ`-a.e. on `O`, using
`0 ≤ G_O(x,y) ≤ (2π)⁻¹ log⁺ (2R/‖y - x‖)`. -/
theorem VolumeGrowth.integrableOn_greenFunction_mul {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R βminus βplus : ℝ} (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) {O : Set ℂ}
    (hOo : IsOpen O) (hO : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ∀ x ∈ closedBall (0 : ℂ) R, IntegrableOn (fun y => greenFunction O x y * f y) O μ := by
  intro x hx
  have hβ : 0 < βplus := hμ.2.1
  obtain ⟨K, hK0, hK⟩ := VolumeGrowth.negMoment_restrict hR hμ hO
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hint := (integrable_norm_sub_rpow_neg hK0 (hK x hx).1).1
  have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x := ae_iff.2 (by simpa using (hK x hx).2)
  have hOb : Bornology.IsBounded O := isBounded_ball.subset hO
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  set c := (2 * Real.pi)⁻¹ * (α⁻¹ * (2 * R) ^ α) with hc_def
  have hc : 0 ≤ c := mul_nonneg hπ (mul_nonneg (inv_nonneg.2 hα.le) (Real.rpow_nonneg (by positivity) _))
  have hdom : Integrable (fun y => |M| * (c * ‖x - y‖ ^ (-α))) (μ.restrict O) :=
    (hint.const_mul _).const_mul _
  refine hdom.mono' ((measurable_greenFunction hOo x).aestronglyMeasurable.mul hf) ?_
  filter_upwards [hne, hfM] with y hyx hy
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have hG0 := greenFunction_nonneg hOb x y
  have hG : greenFunction O x y ≤ c * ‖x - y‖ ^ (-α) := by
    refine (greenFunction_le_posLog_div_norm hR hO x y).trans ?_
    rw [hc_def, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hπ
    refine (posLog_le_inv_mul_rpow (by positivity) hα).trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) hpos.le, Real.rpow_neg (norm_nonneg _), norm_sub_rev, div_eq_mul_inv]
    ring
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG0, mul_comm]
  exact mul_le_mul (hy.trans (le_abs_self M)) hG hG0 (abs_nonneg M)

end GreenGeneral

end HarmonicBalls

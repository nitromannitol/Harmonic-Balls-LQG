import HarmonicBalls.Proofs.Potential.GreenPotentialHolder
import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity
import HarmonicBalls.Proofs.Potential.GreenRegularBoundaryGeometry
import HarmonicBalls.Proofs.Potential.SmoothDomainExteriorSphere
import HarmonicBalls.Proofs.Potential.BoundedDomainGreenMeasurability

/-!
# Green potentials on a smooth bounded open set: the logarithmic potential

Part of the deterministic general-domain Green potential estimate `GreenPotentialGeneralStep`
(Proposition 2.5, Green clause), following the written argument steps4-final Section 1: the logarithmic
potential `V x = ∫ N(x,y) f(y) ν(dy)` of a bounded density against a measure with a uniform negative
moment `∫ ‖x - y‖^(-α) ν(dy) ≤ K` is absolutely convergent and `α`-Hölder (lines 80-124); the Green
potential `x ↦ ∫_O G_O(x,y) f(y) μ(dy)` converges absolutely and is continuous on `closure O`, vanishing on
`frontier O` (uniform integrability of the Green kernel by truncation, Green reciprocity and the exterior-disc
boundary limit).

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

/-! ### Continuity of the Green potential up to the boundary (blueprint G4 + G5)

A family of kernels bounded in `L²(ν)` and converging `ν`-a.e. has convergent potentials against a bounded
density (uniform integrability by truncation at level `L`: `|a - T_L a| ≤ a² / L`). Applied to the Green
kernel `G_O(x, ·)`, whose square is dominated by `c ‖x - y‖^(-α)`, this gives continuity of
`x ↦ ∫_O G_O(x, y) f(y) μ(dy)` on `closure O`, with value `0` on `frontier O`. -/

/-- Truncation at level `L`: `|a - max (-L) (min a L)| ≤ a² / L`. -/
theorem abs_sub_clamp_le {a L : ℝ} (hL : 0 < L) : |a - max (-L) (min a L)| ≤ a ^ 2 / L := by
  rw [le_div_iff₀ hL]
  rcases le_or_gt a L with h1 | h1
  · rcases le_or_gt (-L) a with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2, sub_self, abs_zero, zero_mul]; positivity
    · rw [min_eq_left h1, max_eq_left (by linarith), abs_of_neg (by linarith)]; nlinarith
  · rw [min_eq_right h1.le, max_eq_right (by linarith), abs_of_pos (by linarith)]; nlinarith

/-- `|max (-L) (min a L)| ≤ L` for `L ≥ 0`. -/
theorem abs_clamp_le {a L : ℝ} (hL : 0 ≤ L) : |max (-L) (min a L)| ≤ L :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Truncation error of a potential: for `k ∈ L²(ν)` with `∫ k² dν ≤ K` and `|f| ≤ M`, the potential
`∫ k f dν` converges absolutely and differs from the potential of the truncated kernel by at most `M K / L`. -/
theorem abs_integral_mul_sub_clamp_le {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {k f : α → ℝ} {M K L : ℝ} (hL : 0 < L) (hM : 0 ≤ M) (hk : AEStronglyMeasurable k ν)
    (hk2 : Integrable (fun y => k y ^ 2) ν) (hK : ∫ y, k y ^ 2 ∂ν ≤ K)
    (hf : AEStronglyMeasurable f ν) (hfM : ∀ᵐ y ∂ν, |f y| ≤ M) :
    Integrable (fun y => k y * f y) ν ∧
      |∫ y, k y * f y ∂ν - ∫ y, max (-L) (min (k y) L) * f y ∂ν| ≤ M * K / L := by
  have hcl : Continuous fun a : ℝ => max (-L) (min a L) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hT : Integrable (fun y => max (-L) (min (k y) L) * f y) ν := by
    refine (integrable_const (L * M)).mono' ((hcl.comp_aestronglyMeasurable hk).mul hf) ?_
    filter_upwards [hfM] with y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (abs_clamp_le hL.le) hy (abs_nonneg _) hL.le
  have hbd : ∀ᵐ y ∂ν, ‖(k y - max (-L) (min (k y) L)) * f y‖ ≤ M / L * k y ^ 2 := by
    filter_upwards [hfM] with y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |k y - max (-L) (min (k y) L)| * |f y| ≤ k y ^ 2 / L * M :=
          mul_le_mul (abs_sub_clamp_le hL) hy (abs_nonneg _) (by positivity)
      _ = M / L * k y ^ 2 := by ring
  have hD : Integrable (fun y => (k y - max (-L) (min (k y) L)) * f y) ν :=
    (hk2.const_mul (M / L)).mono' ((hk.sub (hcl.comp_aestronglyMeasurable hk)).mul hf) hbd
  have hsum : ∫ y, k y * f y ∂ν = ∫ y, (k y - max (-L) (min (k y) L)) * f y ∂ν +
      ∫ y, max (-L) (min (k y) L) * f y ∂ν := by
    rw [← integral_add hD hT]
    congr 1
    funext y
    ring
  refine ⟨(hD.add hT).congr (ae_of_all _ fun y => by simp only [Pi.add_apply]; ring), ?_⟩
  rw [hsum, add_sub_cancel_right, ← Real.norm_eq_abs]
  calc ‖∫ y, (k y - max (-L) (min (k y) L)) * f y ∂ν‖ ≤ ∫ y, M / L * k y ^ 2 ∂ν :=
        norm_integral_le_of_norm_le (hk2.const_mul _) hbd
    _ = M / L * ∫ y, k y ^ 2 ∂ν := integral_const_mul _ _
    _ ≤ M / L * K := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = M * K / L := by ring

/-- **Convergence of potentials of `L²`-bounded kernels.** If `k_i → k₀` `ν`-a.e. along a countably
generated filter, with `∫ k_i² dν ≤ K` eventually and `∫ k₀² dν ≤ K`, then `∫ k_i f dν → ∫ k₀ f dν` for every
bounded density `f`. -/
theorem tendsto_integral_mul_of_sq_integral_le {ι α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {l : Filter ι} [l.IsCountablyGenerated] {k : ι → α → ℝ} {k₀ f : α → ℝ}
    {M K : ℝ} (hM : 0 ≤ M)
    (hk : ∀ᶠ i in l, AEStronglyMeasurable (k i) ν ∧ Integrable (fun y => k i y ^ 2) ν ∧
      ∫ y, k i y ^ 2 ∂ν ≤ K)
    (hk₀ : AEStronglyMeasurable k₀ ν) (hk₀2 : Integrable (fun y => k₀ y ^ 2) ν)
    (hK₀ : ∫ y, k₀ y ^ 2 ∂ν ≤ K) (hlim : ∀ᵐ y ∂ν, Filter.Tendsto (fun i => k i y) l (nhds (k₀ y)))
    (hf : AEStronglyMeasurable f ν) (hfM : ∀ᵐ y ∂ν, |f y| ≤ M) :
    Filter.Tendsto (fun i => ∫ y, k i y * f y ∂ν) l (nhds (∫ y, k₀ y * f y ∂ν)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : 0 ≤ K := (integral_nonneg fun y => sq_nonneg (k₀ y)).trans hK₀
  set L := 4 * (M * K + 1) / ε with hL_def
  have hL : 0 < L := by positivity
  have hcl : Continuous fun a : ℝ => max (-L) (min a L) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hDCT : Filter.Tendsto (fun i => ∫ y, max (-L) (min (k i y) L) * f y ∂ν) l
      (nhds (∫ y, max (-L) (min (k₀ y) L) * f y ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => L * M) ?_ ?_
      (integrable_const _) ?_
    · exact hk.mono fun i hi => (hcl.comp_aestronglyMeasurable hi.1).mul hf
    · refine hk.mono fun i _ => ?_
      filter_upwards [hfM] with y hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (abs_clamp_le hL.le) hy (abs_nonneg _) hL.le
    · filter_upwards [hlim] with y hy
      exact ((hcl.tendsto _).comp hy).mul_const _
  have hsmall : M * K / L < ε / 4 := by
    rw [div_lt_iff₀ hL]
    have : ε / 4 * L = M * K + 1 := by rw [hL_def]; field_simp
    linarith
  filter_upwards [Metric.tendsto_nhds.1 hDCT (ε / 2) (by positivity), hk] with i hi hki
  have h1 := abs_le.1 (abs_integral_mul_sub_clamp_le hL hM hki.1 hki.2.1 hki.2.2 hf hfM).2
  have h0 := abs_le.1 (abs_integral_mul_sub_clamp_le hL hM hk₀ hk₀2 hK₀ hf hfM).2
  rw [Real.dist_eq] at hi ⊢
  have h2 := abs_lt.1 hi
  rw [abs_lt]
  constructor <;> linarith

/-- Power bound for the Green kernel: `G_O(x, y) ≤ (2π)⁻¹ β⁻¹ (2R)^β ‖x - y‖^(-β)` for `y ≠ x`,
`O ⊆ B_R`, `β > 0`. -/
theorem greenFunction_le_mul_rpow_neg {O : Set ℂ} {R β : ℝ} (hR : 0 < R) (hO : O ⊆ ball (0 : ℂ) R)
    (hβ : 0 < β) {x y : ℂ} (hyx : y ≠ x) :
    greenFunction O x y ≤ (2 * Real.pi)⁻¹ * (β⁻¹ * (2 * R) ^ β) * ‖x - y‖ ^ (-β) := by
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  refine (greenFunction_le_posLog_div_norm hR hO x y).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hπ
  refine (posLog_le_inv_mul_rpow (by positivity) hβ).trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) hpos.le, Real.rpow_neg (norm_nonneg _), norm_sub_rev, div_eq_mul_inv]
  ring

/-- Smooth bounded open sets are open. -/
theorem isOpen_of_isSmoothBoundedOpen {O : Set ℂ} (hO : IsSmoothBoundedOpen O) : IsOpen O := by
  obtain ⟨-, ρ, hρ, hOρ, -⟩ := hO
  rw [hOρ]
  exact isOpen_lt (hρ.continuous) continuous_const

/-- **Pointwise boundary behaviour of the Green kernel** (blueprint G4, pointwise part). For `y ∈ O` and
`x₀ ∈ closure O` with `x₀ ≠ y`, `G_O(x, y) → G_O(x₀, y)` as `x → x₀` within `closure O`: off the diagonal in
`O` by continuity in the pole, and at `x₀ ∈ frontier O` by Green reciprocity and the exterior-disc boundary
limit (the Green kernel vanishes off `O`). -/
theorem tendsto_greenFunction_nhdsWithin_closure {O : Set ℂ} (hO : IsSmoothBoundedOpen O) {x₀ y : ℂ}
    (hx₀ : x₀ ∈ closure O) (hy : y ∈ O) (hne : y ≠ x₀) :
    Filter.Tendsto (fun x => greenFunction O x y) (nhdsWithin x₀ (closure O))
      (nhds (greenFunction O x₀ y)) := by
  have hOo := isOpen_of_isSmoothBoundedOpen hO
  have hOb : Bornology.IsBounded O := hO.1
  by_cases hx₀O : x₀ ∈ O
  · exact (continuousAt_greenFunction_pole hOo hOb hx₀O hy (Ne.symm hne)).tendsto.mono_left
      nhdsWithin_le_nhds
  rw [greenFunction_of_notMem_left hx₀O, ← union_sdiff_cancel (subset_closure (s := O)),
    nhdsWithin_union]
  refine Filter.Tendsto.sup ?_ ?_
  · obtain ⟨r, hr, hext⟩ := SmoothDomainExteriorSphere.exists_uniform_exterior_ball_of_isSmoothBoundedOpen hO
    have hfr : x₀ ∈ frontier O := by rw [hOo.frontier_eq]; exact ⟨hx₀, hx₀O⟩
    obtain ⟨a, ha, hcl⟩ := hext x₀ hfr
    have hdisj : Disjoint O (ball a r) := by
      refine Set.disjoint_left.2 fun x hxO hxb => ?_
      have h1 := hcl x (subset_closure hxO)
      rw [mem_ball, dist_comm] at hxb
      linarith
    have hcontact : ‖x₀ - a‖ = r := by rw [← dist_eq_norm, dist_comm]; exact ha
    have h := tendsto_greenFunction_zero_of_exterior_disc hOb hy hx₀ hx₀O hr hcontact hdisj
    refine h.congr' (eventually_nhdsWithin_of_forall fun x _ => ?_)
    exact greenFunction_bounded_open_comm hOo hOb y x
  · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    exact (greenFunction_of_notMem_left hx.2 y).symm

/-- **Continuity of the Green potential on `closure O`** (blueprint G4 + G5). For `O` a smooth bounded open
subset of `B_R`, `μ` with the volume growth condition on `B_R`, and `|f| ≤ M` `μ`-a.e. on `O`, the Green
potential `x ↦ ∫_O G_O(x, y) f(y) μ(dy)` is continuous on `closure O`. -/
theorem VolumeGrowth.continuousOn_greenPotential {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R βminus βplus : ℝ} (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ContinuousOn (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O) := by
  intro x₀ hx₀
  have hOo := isOpen_of_isSmoothBoundedOpen hO
  have hβ : 0 < βplus := hμ.2.1
  obtain ⟨K, hK0, hK⟩ := VolumeGrowth.negMoment_restrict hR hμ hOR
  have := isFiniteMeasure_restrict_of_subset_ball (μ := μ) hOR
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  set c := (2 * Real.pi)⁻¹ * ((α / 2)⁻¹ * (2 * R) ^ (α / 2)) with hc_def
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  have hsq : ∀ x ∈ closure O, AEStronglyMeasurable (greenFunction O x) (μ.restrict O) ∧
      Integrable (fun y => greenFunction O x y ^ 2) (μ.restrict O) ∧
      ∫ y, greenFunction O x y ^ 2 ∂μ.restrict O ≤ c ^ 2 * K := by
    intro x hx
    have hint := integrable_norm_sub_rpow_neg hK0 (hK x (hcl hx)).1
    have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x := ae_iff.2 (by simpa using (hK x (hcl hx)).2)
    have hpt : ∀ᵐ y ∂μ.restrict O, ‖greenFunction O x y ^ 2‖ ≤ c ^ 2 * ‖x - y‖ ^ (-α) := by
      filter_upwards [hne] with y hyx
      have hG0 := greenFunction_nonneg (isBounded_ball.subset hOR) x y
      have hG := greenFunction_le_mul_rpow_neg hR hOR (half_pos hα) hyx
      rw [← hc_def] at hG
      have hpow : (‖x - y‖ ^ (-(α / 2))) ^ 2 = ‖x - y‖ ^ (-α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← hpow, ← mul_pow]
      exact pow_le_pow_left₀ hG0 hG 2
    have hmeas := (measurable_greenFunction hOo x).aestronglyMeasurable (μ := μ.restrict O)
    have hI : Integrable (fun y => greenFunction O x y ^ 2) (μ.restrict O) :=
      (hint.1.const_mul _).mono' (hmeas.pow 2) hpt
    refine ⟨hmeas, hI, ?_⟩
    calc ∫ y, greenFunction O x y ^ 2 ∂μ.restrict O ≤ ∫ y, c ^ 2 * ‖x - y‖ ^ (-α) ∂μ.restrict O :=
          integral_mono_ae hI (hint.1.const_mul _)
            (hpt.mono fun y hy => (le_abs_self _).trans (by rwa [← Real.norm_eq_abs]))
      _ = c ^ 2 * ∫ y, ‖x - y‖ ^ (-α) ∂μ.restrict O := integral_const_mul _ _
      _ ≤ c ^ 2 * K := mul_le_mul_of_nonneg_left hint.2 (sq_nonneg _)
  have hlim : ∀ᵐ y ∂μ.restrict O, Filter.Tendsto (fun x => greenFunction O x y)
      (nhdsWithin x₀ (closure O)) (nhds (greenFunction O x₀ y)) := by
    have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x₀ := ae_iff.2 (by simpa using (hK x₀ (hcl hx₀)).2)
    filter_upwards [hne, ae_restrict_mem hOo.measurableSet] with y hyx hyO
    exact tendsto_greenFunction_nhdsWithin_closure hO hx₀ hyO hyx
  exact tendsto_integral_mul_of_sq_integral_le (abs_nonneg M)
    (eventually_nhdsWithin_of_forall hsq) (hsq x₀ hx₀).1 (hsq x₀ hx₀).2.1 (hsq x₀ hx₀).2.2 hlim hf
    (hfM.mono fun y hy => hy.trans (le_abs_self M))

/-! ### Harmonicity of the logarithmic potential minus the Green potential (blueprint G6)

For `ξ, y ∈ O` with `ξ ≠ y`, Green reciprocity identifies `N(ξ, y) - G_O(ξ, y)` with the greatest harmonic minorant
`h_y(ξ)` of the Newton kernel with pole `y`, which is harmonic in `ξ ∈ O`. Hence `V - q = ∫_O h_y(·) f(y) μ(dy)` on
`O`; the kernel is dominated by `A + B ‖ξ - y‖^(-α)`, so the circle mean-value property passes through the
integral by Fubini, and `V - q` is harmonic on `O`. -/

section Harmonic

open InnerProductSpace

/-- Off the diagonal in `O`, `N(ξ, y) - G_O(ξ, y)` is the greatest harmonic minorant of the Newton kernel with
pole `y`, evaluated at `ξ` (Green reciprocity). -/
theorem newtonKernel_sub_greenFunction_eq {O : Set ℂ} (hOo : IsOpen O) (hOb : Bornology.IsBounded O)
    {ξ y : ℂ} (hξ : ξ ∈ O) (hy : y ∈ O) (hne : ξ ≠ y) :
    newtonKernel ξ y - greenFunction O ξ y =
      (greatestHarmonicMinorant O (newtonKernelEReal y) ξ).toReal := by
  have hc : y ∈ O ∧ ξ ∈ O ∧ y ≠ ξ := ⟨hy, hξ, Ne.symm hne⟩
  rw [greenFunction_bounded_open_comm hOo hOb ξ y, newtonKernel_comm ξ y]
  unfold greenFunction
  split_ifs
  ring

/-- Kernel bound: `|N(ξ, y) - G_O(ξ, y)| ≤ A + B ‖ξ - y‖^(-α) + c ‖ξ - y‖^(-α)` for `‖ξ‖, ‖y‖ ≤ R`, `O ⊆ B_R`,
with `A = (2π)⁻¹ α⁻¹ (2R)^α`, `B = (2π)⁻¹ α⁻¹`, `c = (2π)⁻¹ α⁻¹ (2R)^α`. -/
theorem abs_newtonKernel_sub_greenFunction_le {O : Set ℂ} {R α : ℝ} (hR : 0 < R)
    (hO : O ⊆ ball (0 : ℂ) R) (hα : 0 < α) {ξ y : ℂ} (hξ : ‖ξ‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |newtonKernel ξ y - greenFunction O ξ y| ≤
      (2 * Real.pi)⁻¹ * α⁻¹ * (2 * R) ^ α + (2 * Real.pi)⁻¹ * α⁻¹ * ‖ξ - y‖ ^ (-α) +
        (2 * Real.pi)⁻¹ * (α⁻¹ * (2 * R) ^ α) * ‖ξ - y‖ ^ (-α) := by
  have hOb : Bornology.IsBounded O := isBounded_ball.subset hO
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  rcases eq_or_ne ξ y with rfl | hne
  · have h0 : newtonKernel ξ ξ - greenFunction O ξ ξ = 0 := by simp [newtonKernel, greenFunction]
    rw [h0, abs_zero]
    positivity
  have hpos : 0 < ‖ξ - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hG0 := greenFunction_nonneg hOb ξ y
  have hG := greenFunction_le_mul_rpow_neg hR hO hα (Ne.symm hne)
  have hN : |newtonKernel ξ y| ≤ (2 * Real.pi)⁻¹ * (α⁻¹ * (‖ξ - y‖ ^ (-α) + ‖ξ - y‖ ^ α)) := by
    unfold newtonKernel
    rw [abs_mul, abs_neg, abs_of_nonneg hπ]
    exact mul_le_mul_of_nonneg_left (abs_log_le_rpow_neg_add_rpow hpos hα) hπ
  have hle : ‖ξ - y‖ ^ α ≤ (2 * R) ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) hα.le
  have h1 := mul_le_mul_of_nonneg_left hle (mul_nonneg hπ (inv_nonneg.2 hα.le))
  have e : (2 * Real.pi)⁻¹ * (α⁻¹ * (‖ξ - y‖ ^ (-α) + ‖ξ - y‖ ^ α)) =
      (2 * Real.pi)⁻¹ * α⁻¹ * ‖ξ - y‖ ^ (-α) + (2 * Real.pi)⁻¹ * α⁻¹ * ‖ξ - y‖ ^ α := by ring
  calc |newtonKernel ξ y - greenFunction O ξ y| ≤ |newtonKernel ξ y| + |greenFunction O ξ y| :=
        abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg hG0]; linarith

/-- For `r ≠ 0`, almost every `θ` has `circleMap x r θ ≠ y` (the preimage of a point is a coset of `2πℤ`). -/
theorem ae_circleMap_ne {x y : ℂ} {r : ℝ} (hr : r ≠ 0) :
    ∀ᵐ θ ∂(volume : Measure ℝ), circleMap x r θ ≠ y := by
  by_cases h : ∃ θ₀, circleMap x r θ₀ = y
  · obtain ⟨θ₀, hθ₀⟩ := h
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) ((countable_range fun n : ℤ => θ₀ + n * (2 * Real.pi)).measure_zero _)
    have hθ' : circleMap x r θ = circleMap x r θ₀ := (not_not.1 hθ).trans hθ₀.symm
    obtain ⟨n, hn⟩ := (circleMap_eq_circleMap_iff x hr).1 hθ'
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    simp at him
    linarith
  · simp only [not_exists] at h
    exact ae_of_all _ h

/-- **Harmonicity of `V - q`** (blueprint G6). For `O` a smooth bounded open subset of `B_R`, `μ` with the
volume growth condition on `B_R` and `|f| ≤ M` `μ`-a.e. on `O`, the logarithmic potential minus the Green
potential, `x ↦ ∫_O N(x,y) f(y) μ(dy) - ∫_O G_O(x,y) f(y) μ(dy)`, is harmonic on `O`. -/
theorem VolumeGrowth.harmonicOnNhd_newtonPotential_sub_greenPotential {μ : Measure ℂ}
    [IsLocallyFiniteMeasure μ] {R βminus βplus : ℝ} (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus)
    {O : Set ℂ} (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    HarmonicOnNhd (fun x => ∫ y in O, newtonKernel x y * f y ∂μ -
      ∫ y in O, greenFunction O x y * f y ∂μ) O := by
  have hOo := isOpen_of_isSmoothBoundedOpen hO
  have hOb : Bornology.IsBounded O := hO.1
  have hβ : 0 < βplus := hμ.2.1
  obtain ⟨K, hK0, hK⟩ := VolumeGrowth.negMoment_restrict hR hμ hOR
  have := isFiniteMeasure_restrict_of_subset_ball (μ := μ) hOR
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  have hOcl : O ⊆ closedBall (0 : ℂ) R := subset_closure.trans hcl
  have hfM' : ∀ᵐ y ∂μ.restrict O, |f y| ≤ |M| := hfM.mono fun y hy => hy.trans (le_abs_self M)
  obtain ⟨C, -, hVC⟩ := VolumeGrowth.newtonPotential_holder hR hμ hOo.measurableSet hOR
  obtain ⟨hVint, hVhol⟩ := hVC f |M| hf (abs_nonneg M) hfM'
  have hGint := VolumeGrowth.integrableOn_greenFunction_mul hR hμ hOo hOR hf hfM
  have hW : ∀ ξ ∈ closedBall (0 : ℂ) R, (∫ y in O, newtonKernel ξ y * f y ∂μ -
      ∫ y in O, greenFunction O ξ y * f y ∂μ) =
        ∫ y in O, (newtonKernel ξ y - greenFunction O ξ y) * f y ∂μ := by
    intro ξ hξ
    rw [← integral_sub (hVint ξ hξ) (hGint ξ hξ)]
    congr 1
    funext y
    ring
  -- continuity of `V` on `closedBall 0 R` from the Hölder bound, and of `q` on `closure O` (G4 + G5)
  have hVcont : ContinuousOn (fun x => ∫ y in O, newtonKernel x y * f y ∂μ) (closedBall (0 : ℂ) R) := by
    intro x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun x => C * |M| * ‖x - x₀‖ ^ α) (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun x hx => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact hVhol x hx x₀ hx₀
    · have h : Filter.Tendsto (fun x => C * |M| * ‖x - x₀‖ ^ α) (nhdsWithin x₀ (closedBall (0 : ℂ) R))
          (nhds (C * |M| * ‖x₀ - x₀‖ ^ α)) :=
        (((continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr hα.le).tendsto x₀
          |>.const_mul _).mono_left nhdsWithin_le_nhds
      simpa [Real.zero_rpow hα.ne'] using h
  have hcont : ContinuousOn (fun x => ∫ y in O, newtonKernel x y * f y ∂μ -
      ∫ y in O, greenFunction O x y * f y ∂μ) O :=
    (hVcont.mono hOcl).sub
      ((VolumeGrowth.continuousOn_greenPotential hR hμ hO hOR hf hfM).mono subset_closure)
  refine harmonicOnNhd_of_circleAverage_eq hOo hcont fun x hx r hr hxr => ?_
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi' : (2 * Real.pi) ≠ 0 := by positivity
  have hcm : ∀ θ, circleMap x r θ ∈ O := fun θ =>
    hxr (sphere_subset_closedBall (circleMap_mem_sphere x hr.le θ))
  set A := (2 * Real.pi)⁻¹ * α⁻¹ * (2 * R) ^ α with hA_def
  set B := (2 * Real.pi)⁻¹ * α⁻¹ with hB_def
  set c := (2 * Real.pi)⁻¹ * (α⁻¹ * (2 * R) ^ α) with hc_def
  have hA : 0 ≤ A := by positivity
  have hBc : 0 ≤ B + c := by positivity
  have hmeas1 : Measurable fun p : ℝ × ℂ => (circleMap x r p.1, p.2) :=
    ((continuous_circleMap x r).measurable.comp measurable_fst).prodMk measurable_snd
  have hNm : Measurable fun p : ℂ × ℂ => newtonKernel p.1 p.2 := by
    unfold newtonKernel
    fun_prop
  have hDm : Measurable fun p : ℝ × ℂ =>
      newtonKernel (circleMap x r p.1) p.2 - greenFunction O (circleMap x r p.1) p.2 :=
    (hNm.comp hmeas1).sub ((measurable_greenFunction_uncurry hOo).comp hmeas1)
  have htm : Measurable fun p : ℝ × ℂ => ‖circleMap x r p.1 - p.2‖ ^ (-α) :=
    ((((continuous_circleMap x r).measurable.comp measurable_fst).sub measurable_snd).norm).pow_const _
  have hmom : ∀ θ, Integrable (fun y => ‖circleMap x r θ - y‖ ^ (-α)) (μ.restrict O) ∧
      ∫ y, ‖circleMap x r θ - y‖ ^ (-α) ∂μ.restrict O ≤ K := fun θ =>
    integrable_norm_sub_rpow_neg hK0 (hK _ (hOcl (hcm θ))).1
  have htint : Integrable (fun p : ℝ × ℂ => ‖circleMap x r p.1 - p.2‖ ^ (-α))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (μ.restrict O)) := by
    refine (integrable_prod_iff htm.aestronglyMeasurable).2 ⟨ae_of_all _ fun θ => (hmom θ).1, ?_⟩
    refine (integrable_const K).mono' htm.aestronglyMeasurable.norm.integral_prod_right'
      (ae_of_all _ fun θ => ?_)
    have hnn : ∀ y : ℂ, ‖‖circleMap x r θ - y‖ ^ (-α)‖ = ‖circleMap x r θ - y‖ ^ (-α) := fun y =>
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    simp only [hnn]
    rw [Real.norm_of_nonneg (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _)]
    exact (hmom θ).2
  have hFint : Integrable (Function.uncurry fun θ y =>
      (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) * f y)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (μ.restrict O)) := by
    refine ((htint.const_mul (|M| * (B + c))).add (integrable_const (|M| * A))).mono'
      (hDm.aestronglyMeasurable.mul
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)) ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hfM',
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hOo.measurableSet)] with p hp hpO
    have hb := abs_newtonKernel_sub_greenFunction_le hR hOR hα
      (mem_closedBall_zero_iff.1 (hOcl (hcm p.1))) (mem_ball_zero_iff.1 (hOR hpO)).le
    rw [← hA_def, ← hB_def, ← hc_def] at hb
    rw [Real.norm_eq_abs]
    change |(newtonKernel (circleMap x r p.1) p.2 - greenFunction O (circleMap x r p.1) p.2) * f p.2| ≤ _
    rw [abs_mul]
    calc |newtonKernel (circleMap x r p.1) p.2 - greenFunction O (circleMap x r p.1) p.2| * |f p.2|
        ≤ (A + B * ‖circleMap x r p.1 - p.2‖ ^ (-α) + c * ‖circleMap x r p.1 - p.2‖ ^ (-α)) * |M| :=
          mul_le_mul hb hp (abs_nonneg _) (by positivity)
      _ = |M| * (B + c) * ‖circleMap x r p.1 - p.2‖ ^ (-α) + |M| * A := by ring
  have hinner : ∀ᵐ y ∂μ.restrict O, ∫ θ in Ioc 0 (2 * Real.pi),
      (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) * f y =
        2 * Real.pi * ((newtonKernel x y - greenFunction O x y) * f y) := by
    have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x := ae_iff.2 (by simpa using (hK x (hOcl hx)).2)
    filter_upwards [hne, ae_restrict_mem hOo.measurableSet] with y hyx hyO
    have hh := harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hOo hOb hyO
    have hball : HarmonicOnNhd (fun ξ => (greatestHarmonicMinorant O (newtonKernelEReal y) ξ).toReal)
        (closedBall x |r|) := fun z hz => hh z (hxr (by rwa [abs_of_pos hr] at hz))
    have hmv := hball.circleAverage_eq
    rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le hpi] at hmv
    have hI : ∫ θ in Ioc 0 (2 * Real.pi),
        (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) =
          ∫ θ in Ioc 0 (2 * Real.pi),
            (greatestHarmonicMinorant O (newtonKernelEReal y) (circleMap x r θ)).toReal :=
      integral_congr_ae ((ae_restrict_of_ae (ae_circleMap_ne hr.ne')).mono fun θ hθ =>
        newtonKernel_sub_greenFunction_eq hOo hOb (hcm θ) hyO hθ)
    rw [integral_mul_const, hI, ← mul_inv_cancel_left₀ hpi' (∫ θ in Ioc 0 (2 * Real.pi), _), hmv,
      newtonKernel_sub_greenFunction_eq hOo hOb hx hyO (Ne.symm hyx)]
    ring
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le hpi]
  have h1 : ∫ θ in Ioc 0 (2 * Real.pi), (∫ y in O, newtonKernel (circleMap x r θ) y * f y ∂μ -
      ∫ y in O, greenFunction O (circleMap x r θ) y * f y ∂μ) =
        ∫ θ in Ioc 0 (2 * Real.pi), ∫ y in O,
          (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) * f y ∂μ :=
    integral_congr_ae (ae_of_all _ fun θ => hW _ (hOcl (hcm θ)))
  rw [h1, integral_integral_swap hFint, integral_congr_ae hinner, integral_const_mul,
    hW x (hOcl hx), inv_mul_cancel_left₀ hpi']

end Harmonic

end GreenGeneral

end HarmonicBalls

import HarmonicBalls.FirstPass.Phase2.CampbellMarkedExt
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived

/-!
# The LQG measure with a logarithmic insertion, away from the insertion point

For the field `h = h^ℂ - α₀ log |·|` (`fieldCircleAverage`), the circle average of `log |·|` over `∂B_ε(z)` is
`log max(ε, |z|)`, so the regularized measure `ε^{γ²/2} e^{γ h_ε(z)} dz` of the field with insertion `α₀` is the
regularized measure of `h^ℂ` times `max(ε, |z|)^{-γα₀}` (`lqgApprox_fieldCircleAverage_eq_withDensity`). Away from the
origin this weight equals `|z|^{-γα₀}` once `ε < |z|`, so the vague limits satisfy `μ = |z|^{-γα₀} μ₀` against continuous
compactly supported test functions vanishing near `0` (`IsLQGLimit.integral_fieldCircleAverage_eq`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- **The insertion weight of the regularized LQG measure.** For `ε > 0` and a measurable circle-average slice
`h ε`, the regularized measure of the field with insertion `α₀` is the regularized measure of `h` with density
`max(ε, |z|)^{-γα₀}`. -/
theorem lqgApprox_fieldCircleAverage_eq_withDensity {γ α₀ ε : ℝ} (hε : 0 < ε) {h : ℝ → ℂ → ℝ}
    (hm : Measurable (h ε)) :
    lqgApprox γ (fieldCircleAverage α₀ h) ε =
      (lqgApprox γ h ε).withDensity (fun z => ENNReal.ofReal (max ε ‖z‖ ^ (-(γ * α₀)))) := by
  have hF : Measurable fun z : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hm)))
  have hG : Measurable fun z : ℂ => ENNReal.ofReal (max ε ‖z‖ ^ (-(γ * α₀))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.max measurable_norm).pow_const _)
  unfold lqgApprox
  rw [← withDensity_mul _ hF hG]
  congr 1
  funext z
  have hpos : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by positivity), fieldCircleAverage, LocalDecoderCommon.circleAverage_log_norm_eq_max hε z,
    Real.rpow_def_of_pos hpos, mul_assoc, ← Real.exp_add]
  congr 3
  ring

/-- The dyadic scales eventually lie below any positive level. -/
theorem eventually_dyadicScale_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ k : ℕ in atTop, dyadicScale k < δ := by
  have h : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact h.eventually (gt_mem_nhds hδ)

/-- `f · |·|^s` is continuous when `f` is continuous and vanishes near the origin. -/
theorem continuous_mul_norm_rpow_of_zero_notMem {f : ℂ → ℝ} (hf : Continuous f) (h0 : (0 : ℂ) ∉ tsupport f)
    (s : ℝ) : Continuous fun z => f z * ‖z‖ ^ s := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ tsupport f
  · have hz0 : z ≠ 0 := fun h => h0 (h ▸ hz)
    exact hf.continuousAt.mul
      (continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.2 hz0)))
  · have hev : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hev] with w hw
    simp [hw]

/-- **The inserted LQG measure away from the insertion point.** If `μ₀` is the vague limit of the regularized
measures of `h` and `μ` that of the field with insertion `α₀`, then `∫ f dμ = ∫ f(z) |z|^{-γα₀} dμ₀(z)` for every continuous
compactly supported `f` vanishing near `0`. The dyadic slices `h (2^{-k})` are assumed measurable. -/
theorem IsLQGLimit.integral_fieldCircleAverage_eq {γ α₀ : ℝ} {h : ℝ → ℂ → ℝ} {μ₀ μ : Measure ℂ}
    (hm : ∀ k : ℕ, Measurable (h (dyadicScale k))) (hL0 : IsLQGLimit γ h μ₀)
    (hL : IsLQGLimit γ (fieldCircleAverage α₀ h) μ) {f : ℂ → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (h0 : (0 : ℂ) ∉ tsupport f) :
    ∫ z, f z ∂μ = ∫ z, f z * ‖z‖ ^ (-(γ * α₀)) ∂μ₀ := by
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ball (0 : ℂ) δ ⊆ (tsupport f)ᶜ :=
    Metric.isOpen_iff.1 (isClosed_tsupport f).isOpen_compl 0 h0
  have hfar : ∀ z, f z ≠ 0 → δ ≤ ‖z‖ := by
    intro z hz
    by_contra hlt
    have hzb : z ∈ ball (0 : ℂ) δ := by simpa [mem_ball, dist_zero_right] using not_le.1 hlt
    exact hball hzb (subset_tsupport f (by simpa using hz))
  have hg := continuous_mul_norm_rpow_of_zero_notMem hfc h0 (-(γ * α₀))
  have hgs : HasCompactSupport fun z => f z * ‖z‖ ^ (-(γ * α₀)) := hfs.mul_right
  refine tendsto_nhds_unique (hL.tendsto_integral f hfc hfs) ((hL0.tendsto_integral _ hg hgs).congr' ?_)
  filter_upwards [eventually_dyadicScale_lt hδ] with k hk
  have hεk : 0 < dyadicScale k := by unfold dyadicScale; positivity
  have hw : Measurable fun z : ℂ => ENNReal.ofReal (max (dyadicScale k) ‖z‖ ^ (-(γ * α₀))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.max measurable_norm).pow_const _)
  symm
  rw [lqgApprox_fieldCircleAverage_eq_withDensity hεk (hm k),
    integral_withDensity_eq_integral_toReal_smul hw (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : f z = 0
  · simp [hz]
  · have hmax : max (dyadicScale k) ‖z‖ = ‖z‖ := max_eq_right (hk.le.trans (hfar z hz))
    simp only [smul_eq_mul, hmax]
    rw [ENNReal.toReal_ofReal (by positivity), mul_comm]

end HarmonicBalls

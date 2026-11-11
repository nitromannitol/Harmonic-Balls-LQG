import HarmonicBalls.FirstPass.S11c.Dilation

/-!
# Proposition 11.7, the LQG measure under the normalized dilation

If `m` is the γ-LQG measure of the circle profile `h` (vague limit of the approximations
`lqgApprox γ h (dyadicScale k)`, `IsLQGLimit`, Defs/LQG.lean:53), then the measure
`4·2^{γ²/2}e^{-γc} · (push-forward of m under w ↦ 2w)` is the γ-LQG measure of the normalized dilated profile
`h'_e(z) = h_e(z/2) - c` (paper Facts 2.1 III-IV: Weyl scaling and conformal covariance; the constant is the one of
`lqgApprox_dilate_map`). The proof: the approximations transform exactly (`lqgApprox_dilate_map`), the dyadic index shifts
by one (`dyadicScale k / 2 = dyadicScale (k+1)`), and vague convergence is preserved by the push-forward under the
homeomorphism `w ↦ 2w`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

lemma dyadicScale_half (k : ℕ) : dyadicScale k / 2 = dyadicScale (k + 1) := by
  unfold dyadicScale
  rw [pow_succ]
  ring

theorem isLQGLimit_dilate {γ c : ℝ} {hε : ℝ → ℂ → ℝ} (hmeas : ∀ e, Measurable (hε e)) {m : Measure ℂ}
    (hm : IsLQGLimit γ hε m) :
    IsLQGLimit γ (fun e z => hε (e / 2) (z / 2) - c)
      (ENNReal.ofReal (4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c))) • m.map (fun w : ℂ => (2 : ℝ) • w)) := by
  have hσ : Measurable (fun w : ℂ => (2 : ℝ) • w) := measurable_const_smul (2 : ℝ)
  have hσc : Continuous (fun w : ℂ => (2 : ℝ) • w) := continuous_const_smul (2 : ℝ)
  have hK : 0 < 4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c)) := by positivity
  refine ⟨⟨fun x => ?_⟩, fun f hf hfc => ?_⟩
  · -- local finiteness of the push-forward
    obtain ⟨s, hs, hfin⟩ := hm.isLocallyFiniteMeasure.finiteAtNhds ((2 : ℝ)⁻¹ • x)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hs
    set t : Set ℂ := Metric.closedBall ((2 : ℝ)⁻¹ • x) (r / 2) with ht
    have htn : t ∈ 𝓝 ((2 : ℝ)⁻¹ • x) := Metric.closedBall_mem_nhds _ (by linarith)
    have htsub : t ⊆ s := fun z hz => hball (Metric.closedBall_subset_ball (by linarith) hz)
    have htfin : m t < ∞ := (measure_mono htsub).trans_lt hfin
    have hτc : Continuous (fun z : ℂ => (2 : ℝ)⁻¹ • z) := continuous_const_smul _
    have hV : (fun z : ℂ => (2 : ℝ)⁻¹ • z) ⁻¹' t ∈ 𝓝 x := hτc.continuousAt.preimage_mem_nhds htn
    refine ⟨(fun z : ℂ => (2 : ℝ)⁻¹ • z) ⁻¹' t, hV, ?_⟩
    have hVm : MeasurableSet ((fun z : ℂ => (2 : ℝ)⁻¹ • z) ⁻¹' t) :=
      (measurable_const_smul ((2 : ℝ)⁻¹)) (Metric.isClosed_closedBall.measurableSet)
    have hpre : (fun w : ℂ => (2 : ℝ) • w) ⁻¹' ((fun z : ℂ => (2 : ℝ)⁻¹ • z) ⁻¹' t) = t := by
      ext w
      simp only [mem_preimage, smul_smul]
      norm_num
    rw [Measure.smul_apply, Measure.map_apply hσ hVm, hpre, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top htfin
  · -- vague convergence along the dyadic scales
    have hfσ : HasCompactSupport (fun w : ℂ => f ((2 : ℝ) • w)) :=
      hfc.comp_homeomorph (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero)
    have hlim := (hm.tendsto_integral (fun w => f ((2 : ℝ) • w)) (hf.comp hσc) hfσ).comp
      (tendsto_add_atTop_nat 1)
    have hI : ∀ k : ℕ, ∫ z, f z ∂(lqgApprox γ (fun e z => hε (e / 2) (z / 2) - c) (dyadicScale k)) =
        4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c)) *
          ∫ w, f ((2 : ℝ) • w) ∂(lqgApprox γ hε (dyadicScale (k + 1))) := by
      intro k
      rw [lqgApprox_dilate_map γ c (dyadicScale k) hε (dyadicScale_pos k) (hmeas _), dyadicScale_half,
        integral_smul_measure, integral_map hσ.aemeasurable hf.aestronglyMeasurable,
        ENNReal.toReal_ofReal hK.le, smul_eq_mul]
    have hlimK : Tendsto (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ (fun e z => hε (e / 2) (z / 2) - c) (dyadicScale k)))
        atTop (𝓝 (4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c)) * ∫ w, f ((2 : ℝ) • w) ∂m)) := by
      simp_rw [hI]
      exact hlim.const_mul _
    rw [integral_smul_measure, integral_map hσ.aemeasurable hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hK.le, smul_eq_mul]
    exact hlimK

end HarmonicBalls

import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureVersion
import HarmonicBalls.Proofs.Sec8.ExitTimeScaling

/-! # Regularity of normalized pullback measures -/

open Set Metric MeasureTheory Filter
open scoped ENNReal

namespace HarmonicBalls

/-- Positive dilation and a finite positive mass factor preserve the
regularity of a locally finite, atomless, full-support measure. -/
theorem normalizedPullbackMeasure_regular (μ : Measure ℂ)
    (γ α₀ k : ℝ) (hk : 0 < k) (hcirc : ℝ → ℂ → ℝ)
    (hatom : ∀ x : ℂ, μ {x} = 0) (hloc : IsLocallyFiniteMeasure μ)
    (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U) :
    (∀ x : ℂ, normalizedPullbackMeasure γ α₀ k hcirc μ {x} = 0) ∧
      IsLocallyFiniteMeasure (normalizedPullbackMeasure γ α₀ k hcirc μ) ∧
      ∀ U : Set ℂ, IsOpen U → U.Nonempty →
        0 < normalizedPullbackMeasure γ α₀ k hcirc μ U := by
  let : IsLocallyFiniteMeasure μ := hloc
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log k +
    fieldCircleAverage α₀ hcirc k 0)))⁻¹
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Real.exp_pos _))).ne'
  have hct : c ≠ ∞ := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hcont : Continuous (fun x : ℂ => k⁻¹ • x) := by fun_prop
  have hsingle : ∀ x : ℂ, (fun y : ℂ => k⁻¹ • y) ⁻¹' {x} = {k • x} := by
    intro x
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      have h' := congrArg (fun z : ℂ => k • z) h
      simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using h'
    · intro h
      rw [h, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  have hball : ∀ z : ℂ, ∀ r : ℝ,
      normalizedPullbackMeasure γ α₀ k hcirc μ (ball z r) = c * μ (ball (k • z) (k * r)) := by
    intro z r
    change c * (μ.map (fun x : ℂ => k⁻¹ • x)) (ball z r) = _
    rw [map_inv_smul_ball μ hk z r]
  constructor
  · intro x
    change c * (μ.map (fun x : ℂ => k⁻¹ • x)) {x} = 0
    rw [Measure.map_apply hcont.measurable (measurableSet_singleton x), hsingle, hatom, mul_zero]
  constructor
  · refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num), ?_⟩⟩
    rw [hball]
    exact ENNReal.mul_lt_top hct.lt_top measure_ball_lt_top
  · intro U hU ⟨x, hx⟩
    have hpreopen : IsOpen ((fun y : ℂ => k⁻¹ • y) ⁻¹' U) := hU.preimage hcont
    have hprenonempty : ((fun y : ℂ => k⁻¹ • y) ⁻¹' U).Nonempty := by
      refine ⟨k • x, ?_⟩
      simpa only [mem_preimage, smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using hx
    change 0 < c * (μ.map (fun x : ℂ => k⁻¹ • x)) U
    rw [Measure.map_apply hcont.measurable hU.measurableSet]
    exact ENNReal.mul_pos hc0 (hfull _ hpreopen hprenonempty).ne'

end HarmonicBalls

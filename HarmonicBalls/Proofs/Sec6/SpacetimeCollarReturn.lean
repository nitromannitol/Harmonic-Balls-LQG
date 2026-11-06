import HarmonicBalls.Proofs.Sec6.CollarReturnTransport
import HarmonicBalls.Proofs.Sec8.ExitTimeScaling

/-! # Space-time transport of Brownian collar returns

Positive time rescaling and a spatial homeomorphism preserve the return event,
including its witness time. This permits scale-dependent annular estimates to
be reduced to a normalized Brownian return event.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal

/-- Space-time rescaling preserves the core-return event for arbitrary sets. -/
theorem core_return_rescale_iff
    (f : ℂ ≃ₜ ℂ) (c : ℝ≥0) (hc : 0 < c) (A B C : Set ℂ)
    (ω : ContinuousPath ℂ) :
    (∃ t : ℝ≥0, ContinuousPath.exitTime (f '' B) (ContinuousPath.rescale f c ω) ≤
      (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) <
      ContinuousPath.exitTime (f '' A) (ContinuousPath.rescale f c ω) ∧
      (ContinuousPath.rescale f c ω) t ∈ f '' C) ↔
    ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hct : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hA : (c : ℝ≥0∞) * ContinuousPath.exitTime (f '' A) (ContinuousPath.rescale f c ω) =
      ContinuousPath.exitTime A ω := by
    simpa only [preimage_image_eq _ f.injective] using exitTime_rescale_mul f c hc (f '' A) ω
  have hB : (c : ℝ≥0∞) * ContinuousPath.exitTime (f '' B) (ContinuousPath.rescale f c ω) =
      ContinuousPath.exitTime B ω := by
    simpa only [preimage_image_eq _ f.injective] using exitTime_rescale_mul f c hc (f '' B) ω
  constructor
  · rintro ⟨t, htB, htA, htC⟩
    refine ⟨c * t, ?_, ?_, ?_⟩
    · rw [← hB, ENNReal.coe_mul]
      gcongr
    · rw [← hA, ENNReal.coe_mul]
      exact (ENNReal.mul_lt_mul_iff_right hc0 hct).2 htA
    · have htC' : f (ω (c * t)) ∈ f '' C := by simpa only [ContinuousPath.rescale_apply] using htC
      obtain ⟨x, hx, hxeq⟩ := htC'
      exact f.injective hxeq ▸ hx
  · rintro ⟨t, htB, htA, htC⟩
    refine ⟨c⁻¹ * t, ?_, ?_, ?_⟩
    · apply (ENNReal.mul_le_mul_iff_right hc0 hct).1
      rw [hB, ← ENNReal.coe_mul]
      simpa [hc.ne'] using htB
    · apply (ENNReal.mul_lt_mul_iff_right hc0 hct).1
      rw [hA, ← ENNReal.coe_mul]
      simpa [hc.ne'] using htA
    · simpa [ContinuousPath.rescale_apply, hc.ne'] using (mem_image_of_mem f htC)

/-- A space-time path-law identity transports the outer measure of a return
 event, without a measurability assumption on the event. -/
theorem measure_core_return_eq_of_rescale
    (f : ℂ ≃ₜ ℂ) (c : ℝ≥0) (hc : 0 < c) (A B C : Set ℂ)
    (μ ν : Measure (ContinuousPath ℂ))
    (hmap : μ.map (ContinuousPath.rescale f c) = ν) :
    ν {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime (f '' B) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (f '' A) ω ∧ ω t ∈ f '' C} =
    μ {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} := by
  rw [← hmap]
  change (μ.map (continuousPathRescaleHomeomorph f c hc)) _ = _
  rw [(continuousPathRescaleHomeomorph f c hc).measurableEmbedding.map_apply]
  congr 1
  ext ω
  exact core_return_rescale_iff f c hc A B C ω

/-- Brownian dilation preserves core-return probabilities at every positive
scale, for arbitrary domains and core. -/
theorem planarBrownian_core_return_dilation
    {k : ℝ} (hk : 0 < k) (x : ℂ) (A B C : Set ℂ) :
    planarBrownianMotion (k • x)
      {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime ((fun y : ℂ => k • y) '' B) ω ≤
        (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) <
        ContinuousPath.exitTime ((fun y : ℂ => k • y) '' A) ω ∧
        ω t ∈ (fun y : ℂ => k • y) '' C} =
    planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} := by
  have hkn : (0 : ℝ≥0) < ⟨k, hk.le⟩ := by exact_mod_cast hk
  have hc : (0 : ℝ≥0) < ⟨k, hk.le⟩⁻¹ ^ 2 := pow_pos (inv_pos.mpr hkn) 2
  exact measure_core_return_eq_of_rescale (Homeomorph.smulOfNeZero k hk.ne') _ hc A B C
    (planarBrownianMotion x) (planarBrownianMotion (k • x))
    (planarBrownianMotion_map_dilation hk x).symm

end HarmonicBalls.Section6

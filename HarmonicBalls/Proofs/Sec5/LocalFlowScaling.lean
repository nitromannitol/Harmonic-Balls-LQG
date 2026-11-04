import HarmonicBalls.Proofs.Sec5.HausdorffScaling
import HarmonicBalls.Proofs.Sec5.ClusterMeasurability
import HarmonicBalls.Steps.Sec5.ScaleInvariance

/-! # Scaling the local harmonic-ball conditions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

/-- The normalized pullback measure recovers the original mass of a
dilated measurable set after multiplication by the scale factor. -/
theorem normalizedPullbackMeasure_apply_smul
    (γ α₀ : ℝ) {k : ℝ} (hk : 0 < k) (hcirc : ℝ → ℂ → ℝ)
    (μ : Measure ℂ) (A : Set ℂ) (hA : MeasurableSet A) :
    μ (k • A) = ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log k +
      fieldCircleAverage α₀ hcirc k 0))) * normalizedPullbackMeasure γ α₀ k hcirc μ A := by
  have hpre : (fun x : ℂ => k⁻¹ • x) ⁻¹' A = k • A := by
    ext x
    simp only [mem_preimage, mem_smul_set_iff_inv_smul_mem₀ hk.ne']
  let c := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))
  have hc : 0 < c := Real.exp_pos _
  unfold normalizedPullbackMeasure
  change μ (k • A) = ENNReal.ofReal c *
    (ENNReal.ofReal c⁻¹ • Measure.map (fun x : ℂ => k⁻¹ • x) μ) A
  rw [ENNReal.ofReal_inv_of_pos hc]
  rw [Measure.smul_apply, Measure.map_apply (continuous_const_smul k⁻¹).measurable hA, hpre]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top,
    one_mul]

/-- Scaling a local harmonic-ball flow in space and mass preserves its
conditions when the two measures transform accordingly. -/
theorem SatisfiesHarmonicBallConditionsOn.real_smul
    {μ ν : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ} {T k c : ℝ}
    (h : SatisfiesHarmonicBallConditionsOn ν Λ z T)
    (hk : 0 < k) (hc : 0 < c)
    (hmeasure : ∀ A : Set ℂ, MeasurableSet A → μ (k • A) = ENNReal.ofReal c * ν A) :
    SatisfiesHarmonicBallConditionsOn μ (fun t => k • Λ (t / c)) (k • z) (c * T) := by
  have htime : ∀ t ∈ Ioo (0 : ℝ) (c * T), t / c ∈ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨div_pos ht.1 hc, (div_lt_iff₀ hc).2 (by simpa only [mul_comm] using ht.2)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hopen := (h.isRegularOpen (t / c) (htime t ht)).isOpen
    rw [hmeasure _ hopen.measurableSet, h.measure_eq _ (htime t ht), ← ENNReal.ofReal_mul hc.le]
    congr 1
    field_simp
  · intro t ht
    have hfront : frontier (k • Λ (t / c)) = k • frontier (Λ (t / c)) := by
      change frontier ((fun x : ℂ => k • x) '' Λ (t / c)) =
        (fun x : ℂ => k • x) '' frontier (Λ (t / c))
      exact ((Homeomorph.smulOfNeZero k hk.ne').image_frontier (Λ (t / c))).symm
    rw [hfront, hmeasure _ isClosed_frontier.measurableSet,
      h.measure_frontier _ (htime t ht), mul_zero]
  · intro t ht
    unfold IsRegularOpen at *
    rw [closure_smul₀' hk.ne', interior_smul₀ hk.ne', h.isRegularOpen _ (htime t ht)]
  · intro t ht
    exact (h.isBounded _ (htime t ht)).smul₀ k
  · intro t ht
    exact (h.isConnected _ (htime t ht)).image _ (continuous_const_smul k).continuousOn
  · intro t ht
    exact Set.smul_mem_smul_set (h.mem _ (htime t ht))
  · intro s hs t ht hst
    exact smul_set_mono (h.monotoneOn (htime s hs) (htime t ht) (div_le_div_of_nonneg_right hst hc.le))
  · apply h.hausdorffContinuousOn.real_smul_comp k (by fun_prop)
    exact htime
  · apply Subset.antisymm
    · intro x hx
      have hx' : k⁻¹ • x ∈ ⋂ s ∈ Ioo (0 : ℝ) T, Λ s := by
        simp only [mem_iInter]
        intro s hs
        have hcs : c * s ∈ Ioo (0 : ℝ) (c * T) :=
          ⟨mul_pos hc hs.1, mul_lt_mul_of_pos_left hs.2 hc⟩
        have hm := (mem_iInter.mp (mem_iInter.mp hx (c * s)) hcs)
        have heq : c * s / c = s := by field_simp
        rw [heq, mem_smul_set_iff_inv_smul_mem₀ hk.ne'] at hm
        exact hm
      rw [h.iInter_eq, mem_singleton_iff] at hx'
      have := congrArg (fun y : ℂ => k • y) hx'
      simpa only [mem_singleton_iff, smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using this
    · intro x hx
      rw [mem_singleton_iff] at hx
      subst x
      simp only [mem_iInter]
      intro t ht
      exact Set.smul_mem_smul_set (h.mem _ (htime t ht))

/-- The local harmonic-ball conditions transfer from the normalized pullback
measure to the original measure at the corresponding space and time scales. -/
theorem SatisfiesHarmonicBallConditionsOn.normalizedPullback_scale
    {γ α₀ k : ℝ} {hcirc : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    {Λ : ℝ → Set ℂ} {z : ℂ} {T : ℝ} (hk : 0 < k)
    (h : SatisfiesHarmonicBallConditionsOn
      (normalizedPullbackMeasure γ α₀ k hcirc μ) Λ z T) :
    SatisfiesHarmonicBallConditionsOn μ
      (fun t => k • Λ (t / Real.exp (γ * (lqgQ γ * Real.log k +
        fieldCircleAverage α₀ hcirc k 0)))) (k • z)
      (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)) * T) :=
  h.real_smul hk (Real.exp_pos _) (normalizedPullbackMeasure_apply_smul γ α₀ hk hcirc μ)

/-- The local conditions depend only on the flow inside the time interval. -/
theorem SatisfiesHarmonicBallConditionsOn.congr_on
    {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {z : ℂ} {T : ℝ}
    (h : SatisfiesHarmonicBallConditionsOn μ Λ z T)
    (heq : ∀ t ∈ Ioo (0 : ℝ) T, Λ t = Λ' t) :
    SatisfiesHarmonicBallConditionsOn μ Λ' z T := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; rw [← heq t ht]; exact h.measure_eq t ht
  · intro t ht; rw [← heq t ht]; exact h.measure_frontier t ht
  · intro t ht; rw [← heq t ht]; exact h.isRegularOpen t ht
  · intro t ht; rw [← heq t ht]; exact h.isBounded t ht
  · intro t ht; rw [← heq t ht]; exact h.isConnected t ht
  · intro t ht; rw [← heq t ht]; exact h.mem t ht
  · intro s hs t ht hst
    rw [← heq s hs, ← heq t ht]
    exact h.monotoneOn hs ht hst
  · rw [hausdorffContinuousOn_iff_continuousOn_closure]
    have hh := hausdorffContinuousOn_iff_continuousOn_closure.mp h.hausdorffContinuousOn
    apply hh.congr
    intro t ht
    change TopologicalSpace.Closeds.closure (Λ' t) = TopologicalSpace.Closeds.closure (Λ t)
    rw [heq t ht]
  · have hint : (⋂ t ∈ Ioo (0 : ℝ) T, Λ' t) = ⋂ t ∈ Ioo (0 : ℝ) T, Λ t := by
      ext x
      simp only [mem_iInter]
      constructor <;> intro hx t ht
      · rw [heq t ht]; exact hx t ht
      · rw [← heq t ht]; exact hx t ht
    rw [hint, h.iInter_eq]

/-- Local conditions for regularized clusters of a normalized pullback
transfer to the corresponding regularized clusters of the original measure. -/
theorem regularizedClusterConditionsOn_normalizedPullback_scale
    {γ α₀ k R T : ℝ} {hcirc : ℝ → ℂ → ℝ} {μ : Measure ℂ} {z : ℂ} (hk : 0 < k)
    (h : SatisfiesHarmonicBallConditionsOn (normalizedPullbackMeasure γ α₀ k hcirc μ)
      (regularizedCluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z) z T) :
    SatisfiesHarmonicBallConditionsOn μ (regularizedCluster μ (k * R) (k • z)) (k • z)
      (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)) * T) := by
  let c := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))
  have hc : 0 < c := Real.exp_pos _
  have hscaled := h.normalizedPullback_scale hk
  change SatisfiesHarmonicBallConditionsOn μ
    (fun t => k • regularizedCluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z (t / c))
    (k • z) (c * T) at hscaled
  apply hscaled.congr_on
  intro t ht
  have hs := regularizedCluster_comp_real_smul (μ := μ) (R := R) (z := z)
    (c := c⁻¹) hk (inv_pos.mpr hc) ht.1.le
  change regularizedCluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z (c⁻¹ * t) =
    (fun x : ℂ => k • x) ⁻¹' regularizedCluster μ (k * R) (k • z) t at hs
  rw [show t / c = c⁻¹ * t by rw [div_eq_mul_inv, mul_comm], hs]
  exact Set.image_preimage_eq _ (Homeomorph.smulOfNeZero k hk.ne').surjective

end HarmonicBalls

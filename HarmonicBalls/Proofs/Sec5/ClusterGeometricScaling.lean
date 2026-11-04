import HarmonicBalls.Proofs.Sec5.LocalFlowScaling

/-! # Scaling geometric properties of clusters -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

/-- The original cluster is the dilation of the cluster for the normalized
pullback measure, with time changed by the measure scale factor. -/
theorem cluster_normalizedPullback_smul
    {γ α₀ k R t : ℝ} {hcirc : ℝ → ℂ → ℝ} {μ : Measure ℂ} {z : ℂ}
    (hk : 0 < k) (ht : 0 ≤ t) :
    k • cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z
      (t / Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))) =
      cluster μ (k * R) (k • z) t := by
  let c := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))
  have hc : 0 < c := Real.exp_pos _
  have hs := cluster_comp_real_smul (μ := μ) (R := R) (z := z)
    (c := c⁻¹) hk (inv_pos.mpr hc) ht
  change cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z (c⁻¹ * t) =
    (fun x : ℂ => k • x) ⁻¹' cluster μ (k * R) (k • z) t at hs
  change k • cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z (t / c) = _
  rw [show t / c = c⁻¹ * t by rw [div_eq_mul_inv, mul_comm], hs]
  exact Set.image_preimage_eq _ (Homeomorph.smulOfNeZero k hk.ne').surjective

/-- Compact containment and nullity of the cluster frontier transfer from
normalized pullback clusters to the original clusters. -/
theorem cluster_geometricProperties_normalizedPullback_scale
    {γ α₀ k R t : ℝ} {hcirc : ℝ → ℂ → ℝ} {μ : Measure ℂ} {z : ℂ}
    (hk : 0 < k) (ht : 0 ≤ t)
    (hcontain : closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z
      (t / Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)))) ⊆ ball 0 R)
    (hnull : normalizedPullbackMeasure γ α₀ k hcirc μ (frontier
      (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z
        (t / Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))))) = 0) :
    closure (cluster μ (k * R) (k • z) t) ⊆ ball 0 (k * R) ∧
      μ (frontier (cluster μ (k * R) (k • z) t)) = 0 := by
  let A := cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) R z
    (t / Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)))
  have hA : k • A = cluster μ (k * R) (k • z) t := cluster_normalizedPullback_smul hk ht
  refine ⟨?_, ?_⟩
  · rw [← hA, closure_smul₀' hk.ne']
    have hball : k • ball (0 : ℂ) R = ball 0 (k * R) := by
      change (fun x : ℂ => k • x) '' ball 0 R = _
      simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hk] using
        (Metric.smul_image_ball hk.ne' (0 : ℂ) R)
    rw [← hball]
    exact smul_set_mono hcontain
  · have hf : frontier (k • A) = k • frontier A := by
      change frontier ((fun x : ℂ => k • x) '' A) =
        (fun x : ℂ => k • x) '' frontier A
      exact ((Homeomorph.smulOfNeZero k hk.ne').image_frontier A).symm
    rw [← hA, hf, normalizedPullbackMeasure_apply_smul γ α₀ hk hcirc μ _
      isClosed_frontier.measurableSet, hnull, mul_zero]

/-- A uniform local estimate at unit scale transfers to the corresponding
estimate for every centre at a positive spatial scale. -/
theorem uniformLocalClusterProperties_normalizedPullback_scale
    {γ α₀ k H : ℝ} {hcirc : ℝ → ℂ → ℝ} {μ : Measure ℂ} (hk : 0 < k)
    (hlocal : ∀ z ∈ ball (0 : ℂ) (1 / 2),
      SatisfiesHarmonicBallConditionsOn (normalizedPullbackMeasure γ α₀ k hcirc μ)
        (regularizedCluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z) z H ∧
      ∀ t ∈ Ioo (0 : ℝ) H,
        closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t) ⊆ ball 0 1 ∧
        normalizedPullbackMeasure γ α₀ k hcirc μ
          (frontier (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t)) = 0) :
    ∀ z ∈ ball (0 : ℂ) (k / 2),
      SatisfiesHarmonicBallConditionsOn μ (regularizedCluster μ k z) z
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)) * H) ∧
      ∀ t ∈ Ioo (0 : ℝ)
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)) * H),
        closure (cluster μ k z t) ⊆ ball 0 k ∧ μ (frontier (cluster μ k z t)) = 0 := by
  let c := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))
  have hc : 0 < c := Real.exp_pos _
  intro z hz
  have hball : k • ball (0 : ℂ) (1 / 2) = ball 0 (k / 2) := by
    change (fun x : ℂ => k • x) '' ball 0 (1 / 2) = _
    simpa only [smul_zero, Real.norm_eq_abs, abs_of_pos hk, mul_one_div] using
      (Metric.smul_image_ball hk.ne' (0 : ℂ) (1 / 2))
  have hz' : k⁻¹ • z ∈ ball (0 : ℂ) (1 / 2) := by
    apply (mem_smul_set_iff_inv_smul_mem₀ hk.ne' _ _).mp
    rw [hball]
    exact hz
  have heq : k • (k⁻¹ • z) = z := by rw [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  obtain ⟨hflow, hgeom⟩ := hlocal (k⁻¹ • z) hz'
  constructor
  · have h := regularizedClusterConditionsOn_normalizedPullback_scale hk hflow
    simpa only [mul_one, heq] using h
  · intro t ht
    have htime : t / c ∈ Ioo (0 : ℝ) H :=
      ⟨div_pos ht.1 hc, (div_lt_iff₀ hc).2 (by simpa only [mul_comm] using ht.2)⟩
    obtain ⟨hcontain, hnull⟩ := hgeom (t / c) htime
    have h := cluster_geometricProperties_normalizedPullback_scale hk ht.1.le hcontain hnull
    simpa only [mul_one, heq] using h

end HarmonicBalls

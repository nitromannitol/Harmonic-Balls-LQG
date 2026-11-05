import HarmonicBalls.Proofs.Sec5.MassSaturationContinuity

/-! # Right continuity when disc clusters agree -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise ENNReal Topology

universe u

/-- A unit-disc cluster is right-continuous at any positive time when it
has the same closure as the cluster in the disc of radius two. This criterion
does not require a first-contact or full-mass hypothesis. -/
theorem ae_cluster_right_continuity_of_closure_eq_radius_two
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closure (cluster (μ ω) 1 z t) = closure (cluster (μ ω) 2 z t) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  let hC' := affinePairing hC hcirc (2 : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (2 * r) ((2 : ℝ) • z) - hcirc ω 2 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (2 : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul]
    rw [hcirc_eq]
    exact hAff hGFF (2 : ℂ) (by norm_num) 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) :=
    isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ (by norm_num)
  have hcompact := clusterCompactRightContinuity_of_steps (clusterMonotone_proved hI2) h72
    γ α₀ hγ hγ2 hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
    2 (by norm_num)
  filter_upwards [hcompact, hscale] with ω hunit hsc
  intro z hz t ht hclusters
  have hz' : ((2 : ℝ)⁻¹ • z) ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs]
    norm_num at *
    linarith
  have hz1 : ((2 : ℝ)⁻¹ • z) ∈ ball (0 : ℂ) 1 :=
    ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz'
  let A := Real.exp (γ * (lqgQ γ * Real.log 2 + fieldCircleAverage α₀ (hcirc ω) 2 0))
  have hA : 0 < A := Real.exp_pos _
  have hsc' : ∀ s : ℝ, 0 < s →
      cluster (normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) 1 ((2 : ℝ)⁻¹ • z) s =
        (2 : ℝ)⁻¹ • cluster (μ ω) 2 z (A * s) := by
    intro s hs
    simpa [A, smul_smul] using hsc ((2 : ℝ)⁻¹ • z) hz1 s hs
  have hcontained : closure (cluster (μ ω) 2 z t) ⊆ ball 0 2 := by
    rw [← hclusters]
    exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
      isClosed_closedBall).trans (closedBall_subset_ball (by norm_num))
  have hright := cluster_compact_right_continuity_of_scale (by norm_num : (0 : ℝ) < 2)
    hA ht hsc' (hunit ((2 : ℝ)⁻¹ • z) hz' (t / A) (div_pos ht hA)) hcontained
  exact cluster_right_continuity_of_larger_disc_closure_eq (by norm_num : (1 : ℝ) < 2)
    hz ht.le hclusters hright

#print axioms ae_cluster_right_continuity_of_closure_eq_radius_two

end HarmonicBalls

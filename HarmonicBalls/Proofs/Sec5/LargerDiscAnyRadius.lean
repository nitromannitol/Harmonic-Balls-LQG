import HarmonicBalls.Proofs.Sec5.LargerDiscContinuity
import HarmonicBalls.Proofs.Sec5.CompactContinuityAllCentres

/-! # Continuity using any larger disc -/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Pointwise ENNReal Topology
universe u

/-- Equality with a fixed larger-disc cluster closure implies right continuity. -/
theorem ae_cluster_right_continuity_of_closure_eq_larger_disc
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (R : ℝ) (hR : 1 < R)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closure (cluster (μ ω) 1 z t) = closure (cluster (μ ω) R z t) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  let hC' := affinePairing hC hcirc (R : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (R * r) (R • z) - hcirc ω R 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (R : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul, abs_of_pos hRpos]
    rw [hcirc_eq]
    exact hAff hGFF (R : ℂ) (by exact_mod_cast hRpos.ne') 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ R (hcirc ω) (μ ω)) :=
    isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ hRpos
  have hcompact := clusterCompactRightContinuityAllCentres_of_steps (clusterMonotone_proved hI2) h72
    γ α₀ hγ hγ2 hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ R (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
    R hRpos
  filter_upwards [hcompact, hscale] with ω hunit hsc
  intro z hz t ht hclusters
  have hz1 : (R⁻¹ • z) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    have hlt : R⁻¹ < 1 := (inv_lt_one₀ hRpos).2 hR
    nlinarith [norm_nonneg z]
  let A := Real.exp (γ * (lqgQ γ * Real.log R + fieldCircleAverage α₀ (hcirc ω) R 0))
  have hA : 0 < A := Real.exp_pos _
  have hsc' : ∀ s : ℝ, 0 < s →
      cluster (normalizedPullbackMeasure γ α₀ R (hcirc ω) (μ ω)) 1 (R⁻¹ • z) s =
        R⁻¹ • cluster (μ ω) R z (A * s) := by
    intro s hs
    simpa [A, smul_smul, hRpos.ne'] using hsc (R⁻¹ • z) hz1 s hs
  have hcontained : closure (cluster (μ ω) R z t) ⊆ ball 0 R := by
    rw [← hclusters]
    exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
      isClosed_closedBall).trans (closedBall_subset_ball hR)
  have hright := cluster_compact_right_continuity_of_scale hRpos
    hA ht hsc' (hunit (R⁻¹ • z) hz1 (t / A) (div_pos ht hA)) hcontained
  exact cluster_right_continuity_of_larger_disc_closure_eq hR
    hz ht.le hclusters hright



/-- On one full-measure event, equality with any larger-disc closure implies
right continuity. The larger radius may depend on the field, centre and time. -/
theorem ae_cluster_right_continuity_of_exists_larger_disc_closure_eq
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (∃ R : ℝ, 1 < R ∧ closure (cluster (μ ω) 1 z t) =
        closure (cluster (μ ω) R z t)) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  have hevents : ∀ q : {q : ℚ // 1 < (q : ℝ)},
      ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) = closure (cluster (μ ω) (q : ℝ) z t) →
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
          closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
    intro q
    exact ae_cluster_right_continuity_of_closure_eq_larger_disc q q.property hI2 h72
      hAff hCC hγ hγ2 hα hGFF hμ
  filter_upwards [ae_all_iff.mpr hevents] with ω hω
  intro z hz t ht ⟨R, hR, hEq⟩
  obtain ⟨q, hq1, hqR⟩ := exists_rat_btwn hR
  have hzq : z ∈ ball (0 : ℂ) (q : ℝ) := ball_subset_ball hq1.le hz
  have hEqQ : closure (cluster (μ ω) 1 z t) =
      closure (cluster (μ ω) (q : ℝ) z t) := by
    apply Subset.antisymm
    · exact closure_mono (cluster_subset_cluster_larger_disc hq1 hz ht.le)
    · rw [hEq]
      exact closure_mono (cluster_subset_cluster_larger_disc hqR hzq ht.le)
  exact hω ⟨q, hq1⟩ z hz t ht hEqQ


/-- Existence of a larger disc with the same cluster closure implies
Hausdorff continuity, simultaneously for all centres and positive times. -/
theorem ae_cluster_hausdorff_continuity_of_exists_larger_disc_closure_eq
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (∃ R : ℝ, 1 < R ∧ closure (cluster (μ ω) 1 z t) =
        closure (cluster (μ ω) R z t)) →
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
        hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε := by
  filter_upwards [ae_cluster_right_continuity_of_exists_larger_disc_closure_eq hI2 h72 hAff hCC
    hγ hγ2 hα hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hright hmono
  intro z hz t ht hEq
  exact cluster_hausdorffContinuousWithinAt_of_right_continuity ht
    (fun s s' hs hss => hmono s s' 1 hs hss (by norm_num) z hz)
    (hright z hz t ht hEq)

end HarmonicBalls

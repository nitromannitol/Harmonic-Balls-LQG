import HarmonicBalls.Proofs.Sec5.ContactScaledContinuity
import HarmonicBalls.Proofs.Sec7.ClusterIncrementMass
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Continuity at times with no mass loss

A disc cluster with the full prescribed mass has the same closure as a
cluster in any larger disc. Thus compact continuity in the larger disc
applies even if the smaller cluster has already reached its boundary.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise ENNReal Topology

universe u

/-- Full support and conservation of mass identify the closures of nested
clusters in two discs, without compact containment in the smaller disc. -/
theorem cluster_closure_eq_larger_disc_of_mass_eq
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {r R t : ℝ} {z : ℂ}
    (hrR : r < R) (hz : z ∈ ball (0 : ℂ) r) (ht : 0 ≤ t)
    (hsmallopen : IsOpen (cluster μ r z t)) (hlargeopen : IsOpen (cluster μ R z t))
    (hmass : μ (cluster μ r z t) = ENNReal.ofReal t)
    (hupper : μ (cluster μ R z t) ≤ ENNReal.ofReal t) :
    closure (cluster μ r z t) = closure (cluster μ R z t) := by
  have hsub := cluster_subset_cluster_larger_disc (μ := μ) hrR hz ht
  have hnull : μ (cluster μ R z t \ cluster μ r z t) = 0 := by
    apply le_antisymm
    apply measure_sdiff_le_of_measure_le_add hsub hsmallopen.measurableSet.nullMeasurableSet
      (by rw [hmass]; exact ENNReal.ofReal_ne_top)
    simpa [hmass] using hupper
    exact bot_le
  have hnull' : μ (cluster μ R z t \ closure (cluster μ r z t)) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right subset_closure) hnull
  have hlarge : cluster μ R z t ⊆ closure (cluster μ r z t) :=
    sdiff_eq_empty.mp (((hlargeopen.sdiff isClosed_closure).measure_eq_zero_iff μ).mp hnull')
  exact Subset.antisymm (closure_mono hsub) (closure_minimal hlarge isClosed_closure)

/-- Right continuity transfers between nested disc clusters when their
closures agree at the reference time. -/
theorem cluster_right_continuity_of_larger_disc_closure_eq
    {μ : Measure ℂ} {r R t : ℝ} {z : ℂ} (hrR : r < R)
    (hz : z ∈ ball (0 : ℂ) r) (ht : 0 ≤ t)
    (heq : closure (cluster μ r z t) = closure (cluster μ R z t))
    (hright : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ R z s) ⊆ cluster μ R z t + ball (0 : ℂ) ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ r z s) ⊆ cluster μ r z t + ball (0 : ℂ) ε := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hright (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro s hs x hx
  have hx' := hbound s hs ((closure_mono
    (cluster_subset_cluster_larger_disc hrR hz (ht.trans hs.1))) hx)
  obtain ⟨y, hy, v, hv, hxy⟩ := hx'
  have hycl : y ∈ closure (cluster μ r z t) := heq.symm ▸ subset_closure hy
  obtain ⟨w, hw, hyw⟩ := Metric.mem_closure_iff.mp hycl (ε / 2) (half_pos hε)
  refine ⟨w, hw, x - w, ?_, by abel⟩
  rw [mem_ball_zero_iff] at hv ⊢
  have hdist : ‖y - w‖ < ε / 2 := by simpa [dist_eq_norm] using hyw
  have htri := norm_add_le (y - w) v
  have he : x - w = (y - w) + v := by
    change y + v = x at hxy
    rw [← hxy]
    simp only [sub_eq_add_neg]; ac_rfl
  rw [he]
  linarith

/-- At every positive time with the prescribed cluster mass, the cluster is
right-continuous. The two field inputs are staged pending source review. -/
theorem ae_cluster_right_continuity_of_mass_eq
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t →
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
      (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ (by norm_num)
  have hcompact := clusterCompactRightContinuity_of_steps (clusterMonotone_proved hI2) h72
    γ α₀ hγ hγ2 hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
    2 (by norm_num)
  filter_upwards [hcompact, hscale,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hunit hsc hopen hmass hfull
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro z hz t ht hequal
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
  have hz2 : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz
  have hclusters := cluster_closure_eq_larger_disc_of_mass_eq (by norm_num : (1 : ℝ) < 2)
    hz ht.le (hopen t 1 ht (by norm_num) z hz).1 (hopen t 2 ht (by norm_num) z hz2).1
    hequal (hmass 2 t (by norm_num) ht z hz2).1
  have hcontained : closure (cluster (μ ω) 2 z t) ⊆ ball 0 2 := by
    rw [← hclusters]
    exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
      isClosed_closedBall).trans (closedBall_subset_ball (by norm_num))
  have hright := cluster_compact_right_continuity_of_scale (by norm_num : (0 : ℝ) < 2)
    hA ht hsc' (hunit ((2 : ℝ)⁻¹ • z) hz' (t / A) (div_pos ht hA)) hcontained
  exact cluster_right_continuity_of_larger_disc_closure_eq (by norm_num : (1 : ℝ) < 2)
    hz ht.le hclusters hright


/-- Hausdorff continuity holds at every positive time at which the cluster
has the prescribed mass. -/
theorem ae_cluster_hausdorff_continuity_of_mass_eq
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t →
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
        hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε := by
  filter_upwards [ae_cluster_right_continuity_of_mass_eq hI2 h72 hAff hCC
    hγ hγ2 hα hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hright hmono
  intro z hz t ht hmass
  exact cluster_hausdorffContinuousWithinAt_of_right_continuity ht
    (fun s s' hs hss => hmono s s' 1 hs hss (by norm_num) z hz)
    (hright z hz t ht hmass)

/-- A failure of right continuity implies a strict mass deficit for the
unit-disc cluster. -/
theorem ae_mass_deficit_of_not_cluster_right_continuity
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε) →
      μ ω (cluster (μ ω) 1 z t) < ENNReal.ofReal t := by
  filter_upwards [ae_cluster_right_continuity_of_mass_eq hI2 h72 hAff hCC
    hγ hγ2 hα hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hright hmass
  intro z hz t ht hnot
  have hle := (hmass 1 t (by norm_num) ht z hz).1
  have hne : μ ω (cluster (μ ω) 1 z t) ≠ ENNReal.ofReal t := by
    intro heq
    exact hnot (hright z hz t ht heq)
  exact lt_of_le_of_ne hle hne

end HarmonicBalls

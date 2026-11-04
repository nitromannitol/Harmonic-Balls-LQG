import HarmonicBalls.Proofs.Sec6.TruncatedOdometer

/-! # The interior Laplacian of a truncated odometer

On the chosen components the truncation equals the original odometer, and its
Laplacian is the restricted measure. The boundary inequality is separate.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Laplacian

/-- Away from the pole, the odometer has Laplacian `μ` on an open subset of
its cluster. -/
theorem odometer_hasLaplacian_on_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {Λ : Set ℂ} (hΛsub : Λ ⊆ (ball (0 : ℂ) R \ {z}) ∩ cluster μ R z t) :
    HasLaplacian (odometer μ R z t) (μ.restrict Λ) 0 Λ := by
  let : IsLocallyFiniteMeasure μ := hμ
  obtain ⟨hopen, _, ν, _, _, _, _, hΔ⟩ :=
    cluster_open_laplacian_of_general greenFunctionBall obstacleNonCoincidenceHarmonicGeneral_holds
      shiftedOdometerLaplacianGeneral_holds obstacleCompatibilityShiftStep_holds hμ hR hV hz ht
  have hΛball : Λ ⊆ ball (0 : ℂ) R := fun x hx => (hΛsub hx).1.1
  have hΛcluster : Λ ⊆ cluster μ R z t := fun x hx => (hΛsub hx).2
  refine ⟨hΔ.1.mono_set hΛball, fun φ hφ => ?_⟩
  have hφball : IsTestFunction (ball (0 : ℂ) R) φ :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans hΛball⟩
  obtain ⟨hi, _, heq⟩ := hΔ.2 φ hφball
  have hiμ : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hiμΛ : Integrable φ (μ.restrict Λ) := hiμ.mono_measure Measure.restrict_le_self
  refine ⟨hiμΛ, integrable_zero_measure, ?_⟩
  have hφzero (x : ℂ) (hx : x ∉ Λ) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
  have hrest : ∫ x in Λ, φ x ∂μ = ∫ x, φ x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hφzero x hx)
  have hcluster : ∫ x in cluster μ R z t, φ x ∂μ = ∫ x, φ x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hφzero x (fun h => hx (hΛcluster h)))
  have hfront : ∫ x in frontier (cluster μ R z t), φ x ∂ν = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply hφzero x
    intro hxΛ
    have hxI : x ∈ interior (cluster μ R z t) := by
      rw [hopen.interior_eq]
      exact hΛcluster hxΛ
    exact (disjoint_left.mp disjoint_interior_frontier) hxI hx
  have hzΛ : z ∉ Λ := fun hzΛ => (hΛsub hzΛ).1.2 rfl
  have hzφ : φ z = 0 := hφzero z hzΛ
  have hi1 : Integrable φ (μ.restrict (cluster μ R z t)) := hiμ.mono_measure Measure.restrict_le_self
  have hi2 : Integrable φ (ν.restrict (frontier (cluster μ R z t))) :=
    hi.mono_measure (Measure.le_add_left (le_refl _))
  rw [integral_add_measure hi1 hi2, hcluster, hfront, add_zero,
    integral_smul_measure, integral_dirac, hzφ, smul_zero, sub_zero] at heq
  simpa only [integral_zero_measure, sub_zero, hrest] using heq

/-- The componentwise truncation has the same interior Laplacian as the
odometer on the selected components. -/
theorem truncated_odometer_hasLaplacian_on_components
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {Λ : Set ℂ} (hΛopen : IsOpen Λ)
    (hΛsub : Λ ⊆ (ball (0 : ℂ) R \ {z}) ∩ cluster μ R z t) :
    HasLaplacian (Λ.indicator (odometer μ R z t)) (μ.restrict Λ) 0 Λ := by
  apply (odometer_hasLaplacian_on_cluster hμ hR hV hz ht hΛsub).congr_eqOn hΛopen.measurableSet
  intro x hx
  simp [hx]

end HarmonicBalls.Section6

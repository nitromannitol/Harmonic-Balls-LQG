import HarmonicBalls.Proofs.Sec10.PoleAvoidingTruncation
import HarmonicBalls.Proofs.Sec6.TruncatedOdometerDomination

/-! # Riesz domination for a component avoiding the pole -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian
open Section6

universe u

/-- A union of local cluster components that omits the pole has a continuous,
subharmonic zero extension across that pole. -/
theorem odometer_indicator_union_components_continuousOn_and_subharmonic_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) :
    ContinuousOn (Λ.indicator (odometer μ R z t)) U ∧
      IsSubharmonicOn U (Λ.indicator (odometer μ R z t)) := by
  obtain ⟨hc, hs⟩ := odometer_continuousOn_and_subharmonic hμ hR hV hz ht
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  have hG : IsOpen (U ∩ cluster μ R z t) := hU.inter hcluster
  have hΛopen : IsOpen Λ := isOpen_of_union_components hG hΛsub hcomp
  have hdis : Disjoint (frontier Λ) (U ∩ cluster μ R z t) :=
    frontier_union_components_disjoint hG hΛsub hcomp
  have hzcl : z ∈ U → z ∉ closure Λ := by
    intro hzU hzclosure
    have hzfront : z ∈ frontier Λ := by
      rw [hΛopen.frontier_eq]
      exact ⟨hzclosure, hzΛ⟩
    have hzcluster : z ∈ cluster μ R z t := mem_cluster_iff.mpr ⟨hz, Or.inl rfl⟩
    exact disjoint_left.mp hdis hzfront ⟨hzU, hzcluster⟩
  have hΛavoid : Λ ⊆ ball (0 : ℂ) R \ {z} := by
    intro x hx
    refine ⟨hUsub (hΛsub hx).1, ?_⟩
    intro hxz
    have : x = z := mem_singleton_iff.mp hxz
    subst x
    exact hzΛ hx
  apply continuousOn_and_subharmonic_indicator_of_avoided_point hU hΛopen hzcl
    (hc.mono (fun x hx => ⟨hUsub hx.1, hx.2⟩))
  · intro x hx
    exact odometer_nonneg ht.le (ball_subset_closedBall (hΛavoid hx).1) (hΛavoid hx).2
  · intro x hx
    have hxnot : x ∉ cluster μ R z t := fun hxcluster =>
      disjoint_left.mp hdis hx.2 ⟨hx.1.1, hxcluster⟩
    have hnotpos : ¬ 0 < odometer μ R z t x := fun hp =>
      hxnot (mem_cluster_iff.mpr ⟨hUsub hx.1.1, Or.inr hp⟩)
    exact le_antisymm (le_of_not_gt hnotpos)
      (odometer_nonneg ht.le (ball_subset_closedBall (hUsub hx.1.1)) hx.1.2)
  · refine ⟨hs.1.mono hΛavoid, fun x hx r hr hball => ?_⟩
    exact hs.2 x (hΛavoid hx) r hr (hball.trans hΛavoid)

/-- A union of local cluster components avoiding the pole has an odometer
zero extension whose Laplacian dominates the restricted measure. -/
theorem odometer_indicator_union_components_laplacianGE_restrict_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) :
    LaplacianGE (Λ.indicator (odometer μ R z t)) (μ.restrict Λ) U := by
  obtain ⟨hc, hs⟩ :=
    odometer_indicator_union_components_continuousOn_and_subharmonic_of_pole_not_mem
      hμ hR hV hz ht hU hUsub hΛsub hcomp hzΛ
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  have hΛopen : IsOpen Λ := isOpen_of_union_components (hU.inter hcluster) hΛsub hcomp
  have hΛavoid : Λ ⊆ (ball (0 : ℂ) R \ {z}) ∩ cluster μ R z t := by
    intro x hx
    refine ⟨⟨hUsub (hΛsub hx).1, ?_⟩, (hΛsub hx).2⟩
    intro hxz
    have : x = z := mem_singleton_iff.mp hxz
    subst x
    exact hzΛ hx
  have hge : LaplacianGE (Λ.indicator (odometer μ R z t)) 0 U :=
    LaplacianGE.of_laplacianLE_neg
      (laplacianLEOfSuperharmonicStep_holds U _ hU hc.neg hs)
  exact laplacianGE_restrict_of_interior_identity hU hΛopen
    (hΛsub.trans inter_subset_left) hμ hge
    (truncated_odometer_hasLaplacian_on_components hμ hR hV hz ht hΛopen hΛavoid)

/-- The distributional Laplacian of the zero-extended odometer dominates
the measure on a local component that avoids the pole. The ambient open set
may contain the pole. -/
theorem odometer_indicator_component_laplacianGE_restrict_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ R z t)) (hzD : z ∉ D) :
    LaplacianGE (D.indicator (odometer μ R z t)) (μ.restrict D) U := by
  obtain ⟨a, ha, hDa⟩ := hD
  have hDsub : D ⊆ U ∩ cluster μ R z t := by
    rw [← hDa]
    exact connectedComponentIn_subset _ _
  have hcomp : ∀ x ∈ D, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ D := by
    intro x hx
    rw [← hDa] at hx ⊢
    exact (connectedComponentIn_eq hx).symm.subset
  exact odometer_indicator_union_components_laplacianGE_restrict_of_pole_not_mem
    hμ hR hV hz ht hU hUsub hDsub hcomp hzD

/-- Volume growth gives the pole-avoiding Riesz domination simultaneously
for all radii, times, poles, domains and unions of components. -/
theorem ae_odometer_indicator_union_components_laplacianGE_restrict_of_pole_not_mem
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
      ∀ U Λ : Set ℂ, IsOpen U → U ⊆ ball 0 R →
      Λ ⊆ U ∩ cluster (μ ω) R z t →
      (∀ x ∈ Λ, connectedComponentIn (U ∩ cluster (μ ω) R z t) x ⊆ Λ) →
      z ∉ Λ → LaplacianGE (Λ.indicator (odometer (μ ω) R z t)) ((μ ω).restrict Λ) U := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR z hz t ht U Λ hU hUsub hΛsub hcomp hzΛ
  exact odometer_indicator_union_components_laplacianGE_restrict_of_pole_not_mem
    hω.1 hR (hω.2 R hR) hz ht hU hUsub hΛsub hcomp hzΛ

end HarmonicBalls

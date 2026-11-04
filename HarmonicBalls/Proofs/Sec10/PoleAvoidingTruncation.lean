import HarmonicBalls.Proofs.Sec6.TruncatedOdometer
import HarmonicBalls.Proofs.Sec6.LowMass
import HarmonicBalls.Defs.Geometry
import HarmonicBalls.Draft.Section6
import HarmonicBalls.Steps.Sec3.Basic
import HarmonicBalls.Steps.Sec6.LowMass
import HarmonicBalls.Steps.Sec11.SubharmonicMaximum

/-! # Componentwise truncation across an avoided pole -/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set
open Section6

/-- A zero-extended component remains subharmonic across a point which is
locally separated from that component, even if the original function is
only continuous away from the point. -/
theorem continuousOn_and_subharmonic_indicator_of_avoided_point
    {U Λ : Set ℂ} {u : ℂ → ℝ} {z : ℂ}
    (hU : IsOpen U) (hΛ : IsOpen Λ)
    (hz : z ∈ U → z ∉ closure Λ)
    (hcont : ContinuousOn u (U \ {z}))
    (hnonneg : ∀ x ∈ Λ, 0 ≤ u x)
    (hfront : ∀ x ∈ (U \ {z}) ∩ frontier Λ, u x = 0)
    (hsub : IsSubharmonicOn Λ u) :
    ContinuousOn (Λ.indicator u) U ∧ IsSubharmonicOn U (Λ.indicator u) := by
  classical
  let v := Λ.indicator u
  have hvaway : ContinuousOn v (U \ {z}) :=
    continuousOn_indicator_of_zero_frontier hcont hfront
  have hvcont : ContinuousOn v U := by
    intro x hx
    by_cases hxz : x = z
    · subst x
      have hnot : z ∉ closure Λ := hz hx
      have hneigh : (closure Λ)ᶜ ∈ 𝓝 z := isOpen_compl_iff.mpr isClosed_closure |>.mem_nhds hnot
      have heq : (fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝[U] z] v := by
        filter_upwards [nhdsWithin_le_nhds hneigh] with y hy
        have hyΛ : y ∉ Λ := fun hyΛ => hy (subset_closure hyΛ)
        simp [v, hyΛ]
      apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℂ => (0 : ℝ)) U z).congr_of_eventuallyEq heq.symm
      have hzΛ : z ∉ Λ := fun hzΛ => hnot (subset_closure hzΛ)
      simp [v, hzΛ]
    · have hxaway : x ∈ U \ {z} := ⟨hx, by simpa using hxz⟩
      exact ((hvaway x hxaway).continuousAt ((hU.sdiff isClosed_singleton).mem_nhds hxaway)).continuousWithinAt
  have hv0 : ∀ x ∈ U, 0 ≤ v x := by
    intro x hx
    by_cases hxΛ : x ∈ Λ
    · simpa [v, hxΛ] using hnonneg x hxΛ
    · simp [v, hxΛ]
  have hvfront : ∀ x ∈ U ∩ frontier Λ, v x = 0 := by
    intro x hx
    have hxΛ : x ∉ Λ := by
      rw [hΛ.frontier_eq] at hx
      exact hx.2.2
    simp [v, hxΛ]
  have hvsub : IsSubharmonicOn Λ v := hsub.congr (fun x hx => by simp [v, hx])
  have h := isSubharmonicOn_indicator_of_zero_frontier hU hΛ hvcont hv0 hvfront hvsub
  refine ⟨hvcont, ?_⟩
  simpa [v, Set.indicator_indicator] using h

/-- The odometer of a local cluster component which avoids the pole has a
subharmonic zero extension throughout the local domain, including the pole. -/
theorem odometer_indicator_component_continuousOn_and_subharmonic_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ R z t)) (hzD : z ∉ D) :
    ContinuousOn (D.indicator (odometer μ R z t)) U ∧
      IsSubharmonicOn U (D.indicator (odometer μ R z t)) := by
  classical
  obtain ⟨hc, hs⟩ := odometer_continuousOn_and_subharmonic hμ hR hV hz ht
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  let G := U ∩ cluster μ R z t
  have hG : IsOpen G := hU.inter hcluster
  obtain ⟨a, ha, hDa⟩ := hD
  have hDsub : D ⊆ G := by
    rw [← hDa]
    exact connectedComponentIn_subset _ _
  have hDopen : IsOpen D := by
    rw [← hDa]
    exact hG.connectedComponentIn
  have hcomp : ∀ x ∈ D, connectedComponentIn G x ⊆ D := by
    intro x hx
    rw [← hDa] at hx ⊢
    exact (connectedComponentIn_eq hx).symm.subset
  have hdis : Disjoint (frontier D) G :=
    frontier_union_components_disjoint hG hDsub hcomp
  have hzcl : z ∈ U → z ∉ closure D := by
    intro hzU hzclosure
    have hzfront : z ∈ frontier D := by
      rw [hDopen.frontier_eq]
      exact ⟨hzclosure, hzD⟩
    have hzcluster : z ∈ cluster μ R z t := mem_cluster_iff.mpr ⟨hz, Or.inl rfl⟩
    exact disjoint_left.mp hdis hzfront ⟨hzU, hzcluster⟩
  have hDavoid : D ⊆ ball (0 : ℂ) R \ {z} := by
    intro x hx
    refine ⟨hUsub (hDsub hx).1, ?_⟩
    intro hxz
    have : x = z := mem_singleton_iff.mp hxz
    subst x
    exact hzD hx
  apply continuousOn_and_subharmonic_indicator_of_avoided_point hU hDopen hzcl
    (hc.mono (fun x hx => ⟨hUsub hx.1, hx.2⟩))
  · intro x hx
    exact odometer_nonneg ht.le (ball_subset_closedBall (hDavoid hx).1) (hDavoid hx).2
  · intro x hx
    have hxnot : x ∉ cluster μ R z t := fun hxcluster =>
      disjoint_left.mp hdis hx.2 ⟨hx.1.1, hxcluster⟩
    have hnotpos : ¬ 0 < odometer μ R z t x := fun hp =>
      hxnot (mem_cluster_iff.mpr ⟨hUsub hx.1.1, Or.inr hp⟩)
    exact le_antisymm (le_of_not_gt hnotpos)
      (odometer_nonneg ht.le (ball_subset_closedBall (hUsub hx.1.1)) hx.1.2)
  · refine ⟨hs.1.mono hDavoid, fun x hx r hr hball => ?_⟩
    exact hs.2 x (hDavoid hx) r hr (hball.trans hDavoid)

/-- The componentwise disc maximum principle holds without excluding the
pole from the disc's ambient domain, provided the component avoids it. -/
theorem odometerExt_component_iSup_ball_le_iSup_sphere_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    (c : ℂ) {s : ℝ} (hs : 0 < s) (hcontain : closedBall c s ⊆ U) :
    (⨆ x ∈ D ∩ ball c s, odometerExt μ z t x) ≤
      ⨆ x ∈ D ∩ sphere c s, odometerExt μ z t x := by
  obtain ⟨hcont, hsub⟩ :=
    odometer_indicator_component_continuousOn_and_subharmonic_of_pole_not_mem
      hμ zero_lt_one hV hz ht hU hUsub hD hzD
  have hsubball : IsSubharmonicOn (ball c s) (D.indicator (odometer μ 1 z t)) := by
    have hball : ball c s ⊆ U := ball_subset_closedBall.trans hcontain
    exact ⟨hsub.1.mono hball, fun x hx r hr hclosed =>
      hsub.2 x (hball hx) r hr (hclosed.trans hball)⟩
  obtain ⟨y, hy, hmax⟩ := hsubball.exists_maximum_on_sphere hs (hcont.mono hcontain)
  refine iSup_le fun x => iSup_le fun hx => ?_
  have hxz : x ≠ z := by
    intro h
    subst x
    exact hzD hx.1
  have hmaxx := hmax x (ball_subset_closedBall hx.2)
  by_cases hyD : y ∈ D
  · have hyz : y ≠ z := by
      intro h
      subst y
      exact hzD hyD
    have hle : odometer μ 1 z t x ≤ odometer μ 1 z t y := by
      simpa [Set.indicator_of_mem, hx.1, hyD] using hmaxx
    have hle' : odometerExt μ z t x ≤ odometerExt μ z t y := by
      simpa [odometerExt, hxz, hyz] using ENNReal.ofReal_le_ofReal hle
    exact hle'.trans (le_iSup_of_le y (le_iSup_of_le ⟨hyD, hy⟩ le_rfl))
  · have hle : odometer μ 1 z t x ≤ 0 := by
      simpa [Set.indicator_of_mem, Set.indicator_of_notMem, hx.1, hyD] using hmaxx
    have hxzero : odometerExt μ z t x = 0 := by
      simp [odometerExt, hxz, ENNReal.ofReal_eq_zero.mpr hle]
    rw [hxzero]
    exact bot_le

universe u

/-- The disc maximum step of Lemma 6.13 follows from the volume-growth input. -/
theorem componentOdometerDiscMaxStep_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ComponentOdometerDiscMaxStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro z hz t ht ρ hρ x₀ hball D hD c s hs hcontain
  have hUsub : ball x₀ ρ ⊆ ball (0 : ℂ) 1 := fun x hx =>
    (hball (ball_subset_closedBall hx)).1
  have hD' : D ∈ connectedComponentsIn (ball x₀ ρ ∩ cluster (μ ω) 1 z t) := by
    simpa [inter_comm] using hD
  have hzD : z ∉ D := by
    intro hzD
    obtain ⟨a, ha, hDa⟩ := hD'
    have hzball : z ∈ ball x₀ ρ := (connectedComponentIn_subset _ _ (hDa ▸ hzD)).1
    have hznot : z ∉ ({z} : Set ℂ) := (hball (ball_subset_closedBall hzball)).2
    exact hznot (mem_singleton z)
  exact odometerExt_component_iSup_ball_le_iSup_sphere_of_pole_not_mem
    hω.1 (hω.2 1 zero_lt_one) hz ht isOpen_ball hUsub hD' hzD c hs hcontain

/-- Lemma 6.13 from volume growth and the good-annulus decay step. -/
theorem lowMassSmallOdometerStmt_of_volumeGrowth_and_decay
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hdec : GoodAnnulusOdometerDecayStep.{u}) :
    LowMassSmallOdometerStmt.{u} :=
  lowMassSmallOdometerStmt_of_steps hdec (componentOdometerDiscMaxStep_of_volumeGrowth hI2)

end HarmonicBalls

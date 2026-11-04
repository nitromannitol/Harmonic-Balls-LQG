import HarmonicBalls.Proofs.Sec10.PoleAvoidingTruncation

/-! # Boundary suprema for pole-avoiding components -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- A continuous extended-nonnegative-valued function on an open set is
bounded at closure points by its supremum on the original set. -/
theorem continuousOn_le_iSup_of_mem_closure {U S : Set ℂ} {f : ℂ → ℝ≥0∞}
    (hU : IsOpen U) (hcont : ContinuousOn f U)
    {x : ℂ} (hx : x ∈ U) (hxS : x ∈ closure S) :
    f x ≤ ⨆ y ∈ S, f y := by
  let M : ℝ≥0∞ := ⨆ y ∈ S, f y
  have hm : MapsTo f S (Iic M) := by
    intro y hy
    change f y ≤ M
    dsimp [M]
    exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)
  have hc : ContinuousWithinAt f S x :=
    ((hcont x hx).continuousAt (hU.mem_nhds hx)).continuousWithinAt
  have := hc.mem_closure hxS hm
  simpa [isClosed_Iic.closure_eq] using this

/-- The closure of a pole-avoiding local cluster component cannot reach the
pole inside its local domain. -/
theorem pole_not_mem_closure_component_in_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    (hzU : z ∈ U) : z ∉ closure D := by
  have hcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  let G := U ∩ cluster μ 1 z t
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
  have hdis : Disjoint (frontier D) G := frontier_union_components_disjoint hG hDsub hcomp
  intro hzcl
  have hzfront : z ∈ frontier D := by
    rw [hDopen.frontier_eq]
    exact ⟨hzcl, hzD⟩
  have hzcluster : z ∈ cluster μ 1 z t := mem_cluster_iff.mpr ⟨hz, Or.inl rfl⟩
  exact disjoint_left.mp hdis hzfront ⟨hzU, hzcluster⟩

/-- At every local closure point of a subset of a pole-avoiding component,
the odometer is bounded by its supremum on that subset. -/
theorem odometerExt_le_iSup_component_of_mem_closure_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {S : Set ℂ} (hSD : S ⊆ D) {x : ℂ} (hxU : x ∈ U) (hxS : x ∈ closure S) :
    odometerExt μ z t x ≤ ⨆ y ∈ S, odometerExt μ z t y := by
  have hxz : x ≠ z := by
    intro e
    subst x
    exact pole_not_mem_closure_component_in_domain hμ hV hz ht hU hD hzD hxU (closure_mono hSD hxS)
  have hcont := (odometer_continuousOn_and_subharmonic hμ zero_lt_one hV hz ht).1
  have hcont' : ContinuousOn (fun y => ENNReal.ofReal (odometer μ 1 z t y)) (U \ {z}) :=
    ENNReal.continuous_ofReal.continuousOn.comp
      (hcont.mono (fun y hy => ⟨hUsub hy.1, hy.2⟩)) (mapsTo_univ _ _)
  have hbound := continuousOn_le_iSup_of_mem_closure
    (hU.sdiff isClosed_singleton) hcont' (show x ∈ U \ {z} from ⟨hxU, by simpa using hxz⟩) hxS
  simp only [odometerExt, hxz, ↓reduceIte]
  refine hbound.trans (iSup_le fun y => iSup_le fun hy => ?_)
  have hyz : y ≠ z := fun e => hzD (e ▸ hSD hy)
  exact le_iSup₂_of_le y hy (by simp [hyz])


/-- Closure values of an annular subset of a pole-avoiding component are
controlled by the odometer supremum on that component inside the annulus. -/
theorem odometerExt_iSup_closure_le_iSup_inter_of_pole_not_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D S A : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    (hS : S ⊆ D ∩ A) :
    (⨆ x ∈ U ∩ closure S, odometerExt μ z t x) ≤
      ⨆ x ∈ D ∩ A, odometerExt μ z t x := by
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact (odometerExt_le_iSup_component_of_mem_closure_of_pole_not_mem
    hμ hV hz ht hU hUsub hD hzD (hS.trans inter_subset_left) hx.1 hx.2).trans
      (biSup_mono fun y hy => hS hy)


/-- A pointwise odometer bound on a circle propagates to the disc for a
pole-avoiding local component, even when the disc contains the pole. -/
theorem component_odometer_iSup_ball_le_of_sphere_bound
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {w : ℂ} {r : ℝ} (hr : 0 < r) (hcontain : closedBall w r ⊆ U)
    {M : ℝ≥0∞} (hsphere : ∀ x ∈ D ∩ sphere w r, odometerExt μ z t x ≤ M) :
    (⨆ x ∈ D ∩ ball w r, odometerExt μ z t x) ≤ M := by
  exact (odometerExt_component_iSup_ball_le_iSup_sphere_of_pole_not_mem
    hμ hV hz ht hU hUsub hD hzD w hr hcontain).trans
      (iSup_le fun x => iSup_le fun hx => hsphere x hx)

end HarmonicBalls

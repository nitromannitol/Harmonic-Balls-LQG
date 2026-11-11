import HarmonicBalls.Proofs.Sec5.GreenConnectedComponent
import HarmonicBalls.Proofs.Sec5.CountableDiscCompatibility

/-! # Supersolutions on connected components -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- An admissible least supersolution on the pole component extends by zero
to an admissible supersolution on the entire bounded open domain. -/
theorem exists_leastSupersolutionOn_component_extension
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    ∃ w ∈ supersolutionsOn μ U z t,
      EqOn w (leastSupersolutionOn μ (connectedComponentIn U z) z t)
        (connectedComponentIn U z) := by
  classical
  let V := connectedComponentIn U z
  let W := U \ V
  let v := leastSupersolutionOn μ V z t
  let w : ℂ → ℝ := fun x => if x ∈ V then v x else 0
  have hV : IsOpen V := hU.connectedComponentIn
  have hW : IsOpen W := IsOpen.sdiff_connectedComponentIn hU z
  have hsub : V ⊆ U := connectedComponentIn_subset U z
  have hzV : z ∈ V := mem_connectedComponentIn hz
  have hzero : ∀ x ∈ frontier V, v x = 0 := by
    intro x hx
    have hxnot : x ∉ V := by
      have hi : x ∉ interior V := hx.2
      simpa [hV.interior_eq] using hi
    have hxz : x ≠ z := fun e => hxnot (e ▸ hzV)
    exact leastSupersolutionOn_eq_zero_of_boundary (hUb.subset hsub) ht hx.1 hxnot hxz
  have hcont : ContinuousOn w (closure U) := by
    dsimp only [w]
    apply ContinuousOn.if
    · intro x hx
      exact hzero x hx.2
    · exact hv.1.mono inter_subset_right
    · exact continuousOn_const
  have hLV : LaplacianLE w μ V := by
    apply hv.2.1.congr_eqOn hV.measurableSet
    intro x hx
    change x ∈ V at hx
    change v x = w x
    simp [w, hx]
  have hLW : LaplacianLE w μ W := by
    apply (laplacianLE_zero μ W).congr_eqOn hW.measurableSet
    intro x hx
    simp [w, hx.2]
  have hsplit : V ∪ W = U := union_sdiff_cancel hsub
  have hL : LaplacianLE w μ U := hsplit ▸ LaplacianLE.union hV hW hLV hLW
  refine ⟨w, ⟨hcont, hL, ?_⟩, ?_⟩
  · intro x hx hxz
    by_cases hxV : x ∈ V
    · rw [greenFunction_eq_connectedComponentIn_all hU hUb hz]
      simpa [w, hxV] using hv.2.2 x (subset_closure hxV) hxz
    · have hG := greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz hxV
      simp [w, hxV, hG]
  · intro x hx
    change x ∈ V at hx
    change w x = v x
    simp [w, hx]

/-- The cluster depends only on the pole component when its least
supersolution is admissible. -/
theorem clusterOn_eq_connectedComponentIn_of_leastSupersolutionOn_mem
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    clusterOn μ U z t = clusterOn μ (connectedComponentIn U z) z t := by
  apply subset_antisymm
  · intro x hx
    have hxV := clusterOn_subset_connectedComponentIn hU hUb hz ht hx
    refine ⟨hxV, ?_⟩
    by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      obtain ⟨w, hw, heq⟩ := exists_leastSupersolutionOn_component_extension hU hUb hz ht hv
      have hle := leastSupersolutionOn_le_of_mem hw (subset_closure hx.1) hxz
      rw [heq hxV] at hle
      rw [← greenFunction_eq_connectedComponentIn_all hU hUb hz]
      exact (hx.2.resolve_left hxz).trans_le hle
  · exact clusterOn_connectedComponentIn_subset hU hUb hz ht

/-- If the pole component is a disc, the full-domain cluster equals the disc
cluster, independently of the other components. -/
theorem clusterOn_eq_disc_of_connectedComponentIn_eq_ball
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {R βm βp t : ℝ} {z : ℂ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hz : z ∈ U) (hcomp : connectedComponentIn U z = ball (0 : ℂ) R) (ht : 0 < t) :
    clusterOn μ U z t = cluster μ R z t := by
  have hzR : z ∈ ball (0 : ℂ) R := hcomp ▸ mem_connectedComponentIn hz
  have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hzR ht).2.2
  have heq : leastSupersolutionOn μ (ball (0 : ℂ) R) z t = leastSupersolution μ R z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne']
  have hv' : leastSupersolutionOn μ (ball (0 : ℂ) R) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R) z t := by
    rw [heq, supersolutionsOn_ball μ hR.ne']
    exact hv
  rw [clusterOn_eq_connectedComponentIn_of_leastSupersolutionOn_mem hU hUb hz ht.le
    (hcomp.symm ▸ hv'), hcomp, clusterOn_ball μ hR.ne']

/-- Strong compatibility holds on a bounded open domain whose pole component
is a disc, under either compact-containment alternative. -/
theorem regularizedFamily_strongCompatibility_of_connectedComponentIn_eq_ball
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ U)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  have hzR : z ∈ ball (0 : ℂ) R := hcomp ▸ mem_connectedComponentIn hz
  have hc := clusterOn_eq_disc_of_connectedComponentIn_eq_ball hμ hU hUb hR (hV R hR) hz hcomp ht
  have hconnected : IsConnected (cluster μ R z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR (hV R hR) z hzR t ht).2.2.1]
    exact (obstacleNonCoincidenceHarmonicGeneral_holds μ hμ R βm βp hR (hV R hR) z hzR t ht).2.1
  have hcompact : closure (Λ t) ⊆ ball (0 : ℂ) R ∨
      closure (clusterOn μ (ball (0 : ℂ) R) z t) ⊆ ball 0 R := by
    rcases hcl with hcl | hcl
    · left
      rw [← hcomp]
      exact (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
        (subset_closure (hΛ.1.mem t ht)) hcl
    · right
      rw [clusterOn_ball μ hR.ne', ← hcomp]
      apply hconnected.isPreconnected.closure.subset_connectedComponentIn
      · exact subset_closure ⟨hzR, Or.inl rfl⟩
      · simpa only [hc] using hcl
  have h := regularizedFamily_strongCompatibility_relative_countable_disc hμ hV hR ∅
    (by simp) (by simp)
    (by simpa using hzR) ht hΛ (by simpa using hcompact)
  simpa only [sdiff_empty, clusterOn_ball μ hR.ne', hc] using h



end HarmonicBalls

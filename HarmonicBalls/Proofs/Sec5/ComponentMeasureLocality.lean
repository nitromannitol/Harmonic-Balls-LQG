import HarmonicBalls.Proofs.Sec5.ComponentClipping
import HarmonicBalls.Proofs.Sec5.CompactStrongCompatibility

/-! # Locality on the pole component -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- A set contained in a component cannot accumulate inside a different
component of an open planar domain. -/
theorem closure_subset_connectedComponentIn_of_subset
    {U A : Set ℂ} (hU : IsOpen U) {z : ℂ}
    (hA : A ⊆ connectedComponentIn U z) (hcl : closure A ⊆ U) :
    closure A ⊆ connectedComponentIn U z := by
  have hW := IsOpen.sdiff_connectedComponentIn hU z
  have hclosed : IsClosed (U \ connectedComponentIn U z)ᶜ := hW.isClosed_compl
  have hsub : A ⊆ (U \ connectedComponentIn U z)ᶜ := by
    intro x hx hxW
    exact hxW.2 (hA hx)
  have hcl' := closure_minimal hsub hclosed
  intro x hx
  by_contra hxV
  exact hcl' hx ⟨hcl hx, hxV⟩

/-- Bounded open domains with the same pole component produce the same
cluster when the measures agree on that component. -/
theorem clusterOn_eq_of_connectedComponentIn_eq_of_restrict_eq
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    {z : ℂ} (hzU : z ∈ U) (hzV : z ∈ V)
    (hcomp : connectedComponentIn U z = connectedComponentIn V z)
    (hμν : μ.restrict (connectedComponentIn U z) =
      ν.restrict (connectedComponentIn U z)) {t : ℝ} (ht : 0 ≤ t) :
    clusterOn μ U z t = clusterOn ν V z t := by
  rw [clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hVμ hU hUb hzU ht,
    clusterOn_eq_connectedComponentIn_of_volumeGrowth hν hVν hV hVb hzV ht,
    ← hcomp]
  exact clusterOn_eq_of_restrict_eq hU.connectedComponentIn.measurableSet hμν z t

/-- If the pole-component obstacle is admissible and the full-domain cluster
is compactly contained, a regularized family depends only on the measure in
the pole component. -/
theorem regularizedFamily_eq_of_restrict_connectedComponentIn
    {μ ν : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hμν : μ.restrict (connectedComponentIn U z) =
      ν.restrict (connectedComponentIn U z))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hopenμ : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hopenν : ∀ r : ℝ, 0 < r → IsOpen (cluster ν r z t))
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    Λ t = Λ' t := by
  have hc := clusterOn_eq_connectedComponentIn_of_leastSupersolutionOn_mem
    hU hUb hz ht.le hv
  have hsmall : closure (clusterOn μ (connectedComponentIn U z) z t) ⊆
      connectedComponentIn U z := by
    rw [← hc]
    exact closure_subset_connectedComponentIn_of_subset hU
      (clusterOn_subset_connectedComponentIn hU hUb hz ht.le) hcl
  exact regularizedFamily_eq_of_restrict_eq_of_clusterOn_compact_containment
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z)) hμν
    (mem_connectedComponentIn hz) ht hΛ hΛ' hopenμ hopenν hv hsmall

/-- Strong compatibility follows from admissibility and boundary regularity
of the pole component, irrespective of the other components. -/
theorem regularizedFamily_strongCompatibility_of_component_boundary
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  have hc := clusterOn_eq_connectedComponentIn_of_leastSupersolutionOn_mem
    hU hUb hz ht.le hv
  have hVb := hUb.subset (connectedComponentIn_subset U z)
  have hzV := mem_connectedComponentIn hz
  rcases hcl with hcl | hcl
  · have hΛV : closure (Λ t) ⊆ connectedComponentIn U z :=
      (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
        (subset_closure (hΛ.1.mem t ht)) hcl
    obtain ⟨r₁, hr₁⟩ := hVb.subset_ball (0 : ℂ)
    obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
    let r := max 1 (max r₁ r₂) + 1
    have hr : 0 < r := by dsimp [r]; linarith [le_max_left (1 : ℝ) (max r₁ r₂)]
    have hr₁r : r₁ ≤ r := by
      dsimp [r]; linarith [(le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
    have hr₂r : r₂ ≤ r := by
      dsimp [r]; linarith [(le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
    have hVr : connectedComponentIn U z ⊆ ball (0 : ℂ) r :=
      hr₁.trans (ball_subset_ball hr₁r)
    have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
    have hrepr := hΛ.2.2 t ht r hr hΛr r le_rfl
    have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
      rw [hrepr, closure_regularizedCluster_eq_of_isOpen (hopen r hr)]
    obtain ⟨h, hcont, hh, hG⟩ :=
      exists_continuousOn_green_difference_of_boundary_limits
        hU.connectedComponentIn hVr hzV hboundary
    have heq := clusterOn_eq_cluster_of_green_difference_of_nonneg
      hU.connectedComponentIn hVr hzV ht.le hv hcont hh hG
      (Or.inl (hcluster ▸ hΛV))
    rw [hc, heq, ← hcluster]
  · have hsmall : closure (clusterOn μ (connectedComponentIn U z) z t) ⊆
        connectedComponentIn U z := by
      rw [← hc]
      exact closure_subset_connectedComponentIn_of_subset hU
        (clusterOn_subset_connectedComponentIn hU hUb hz ht.le) hcl
    rw [hc]
    exact regularizedFamily_closure_eq_clusterOn_of_compact_containment
      hU.connectedComponentIn hVb hzV ht hΛ hopen hv hsmall


end HarmonicBalls

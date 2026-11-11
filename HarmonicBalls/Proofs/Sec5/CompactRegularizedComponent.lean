import HarmonicBalls.Proofs.Sec5.MinimumLaplacianGluing

/-! # Compact regularized clusters and admissibility -/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- A compactly contained regularized cluster forces admissibility of the
least supersolution on a bounded Green-regular domain. -/
theorem leastSupersolutionOn_mem_of_compact_regularizedFamily
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t := by
  obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_left (1 : ℝ) (max r₁ r₂)]
  have hr₁r : r₁ ≤ r := by
    dsimp [r]; linarith [(le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
  have hr₂r : r₂ ≤ r := by
    dsimp [r]; linarith [(le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have hrepr := hΛ.2.2 t ht r hr hΛr r le_rfl
  have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hrepr, closure_regularizedCluster_eq_of_isOpen
      (isOpen_cluster_of_volumeGrowth hμ hV ht r hr (hUr hz))]
  exact leastSupersolutionOn_mem_of_compact_disc_cluster_of_volumeGrowth
    hμ hU hr (hV r hr) hUr hz ht hboundary (hcluster ▸ hcl)

/-- Compact containment in the deleted domain gives compatibility after a
relatively countable deletion, without assuming admissibility of either
least supersolution. -/
theorem regularizedFamily_closure_eq_of_countable_on_component_of_boundary
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hclU : closure (Λ t) ⊆ U := hcl.trans sdiff_subset
  have hclC : closure (Λ t) ⊆ connectedComponentIn U z :=
    (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (hΛ.1.mem t ht)) hclU
  have hw := leastSupersolutionOn_mem_of_compact_regularizedFamily hμ hV
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary hΛ hclC
  exact regularizedFamily_strongCompatibility_of_countable_on_component_of_volumeGrowth
    hμ hV hU hUK hUb ht hz hK hw hboundary hΛ (Or.inl hcl)

/-- The boundary regularity condition holds when the pole component is an
intersection of discs. -/
theorem regularizedFamily_closure_eq_of_countable_on_disc_intersection_component
    {ι : Type*} {c : ι → ℂ} {r : ι → ℝ}
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hcomp : connectedComponentIn U z = ⋂ i, ball (c i) (r i))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  exact regularizedFamily_closure_eq_of_countable_on_component_of_boundary
    hμ hV hU hUK hUb ht hz hK
    (tendsto_greenFunction_zero_of_enclosing_discs (mem_connectedComponentIn hz.1)
      (exists_enclosing_disc_of_eq_iInter_ball hcomp)) hΛ hcl


end HarmonicBalls

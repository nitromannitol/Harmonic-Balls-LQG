import HarmonicBalls.Proofs.Sec5.RegularizedCountableRemoval

/-! # Exact cluster removal for compact regularized clusters -/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- A compactly contained regularized cluster forces exact cluster removal
under relatively countable deletion, without an admissibility hypothesis. -/
theorem clusterOn_sdiff_eq_of_compact_regularizedFamily_of_boundary
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
    (hcl : closure (Λ t) ⊆ U) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  have hclC : closure (Λ t) ⊆ connectedComponentIn U z :=
    (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (hΛ.1.mem t ht)) hcl
  have hw := leastSupersolutionOn_mem_of_compact_regularizedFamily hμ hV
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary hΛ hclC
  exact clusterOn_sdiff_of_countable_on_component hμ hV hU hUK hUb ht.le hz hK hw

/-- Two relatively countable deletions give the same cluster away from their
union, and their closures agree, even when the deleted points meet the cluster. -/
theorem clusterOn_two_countable_deletions_of_compact_regularizedFamily
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K L : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUL : IsOpen (U \ L)) (hUb : Bornology.IsBounded U)
    {t : ℝ} {z : ℂ} (ht : 0 < t) (hzK : z ∈ U \ K) (hzL : z ∈ U \ L)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hL : (L ∩ connectedComponentIn U z).Countable)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    (clusterOn μ (U \ K) z t \ L = clusterOn μ (U \ L) z t \ K) ∧
    (closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ (U \ L) z t)) := by
  have heqK := clusterOn_sdiff_eq_of_compact_regularizedFamily_of_boundary
    hμ hV hU hUK hUb ht hzK hK hboundary hΛ hcl
  have heqL := clusterOn_sdiff_eq_of_compact_regularizedFamily_of_boundary
    hμ hV hU hUL hUb ht hzL hL hboundary hΛ hcl
  constructor
  · rw [heqK, heqL]
    ext x
    simp only [Set.mem_sdiff]
    tauto
  · have h1 := regularizedFamily_closure_eq_sdiff_of_compact_original_of_boundary
      hμ hV hU hUK hUb ht hzK hK hboundary hΛ hcl
    have h2 := regularizedFamily_closure_eq_sdiff_of_compact_original_of_boundary
      hμ hV hU hUL hUb ht hzL hL hboundary hΛ hcl
    exact h1.symm.trans h2


end HarmonicBalls

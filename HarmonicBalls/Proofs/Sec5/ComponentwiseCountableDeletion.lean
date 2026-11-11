import HarmonicBalls.Proofs.Sec5.ComponentCountableDiscCompatibility
import HarmonicBalls.Proofs.Sec10.CountableDeletionCrossings

/-! # Componentwise countable deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Deletions elsewhere in an open planar set cannot affect its pole component;
countable deletion within that component preserves its connectedness. -/
theorem connectedComponentIn_sdiff_of_countable_on_component {U K : Set ℂ}
    (hU : IsOpen U) {z : ℂ} (hz : z ∈ U \ K)
    (hK : (K ∩ connectedComponentIn U z).Countable) :
    connectedComponentIn (U \ K) z = connectedComponentIn U z \ K := by
  have hpre := isPreconnected_sdiff_countable_of_isOpen
    hU.connectedComponentIn isPreconnected_connectedComponentIn hK
  apply Subset.antisymm
  · intro y hy
    exact ⟨connectedComponentIn_mono z sdiff_subset hy,
      (connectedComponentIn_subset _ _ hy).2⟩
  · exact hpre.subset_connectedComponentIn
      ⟨mem_connectedComponentIn hz.1, hz.2⟩ (by
        intro y hy
        exact ⟨connectedComponentIn_subset U z hy.1, hy.2⟩)

/-- For a domain with a disc pole component, arbitrary deletion outside that
component and countable deletion inside it leave the indicated disc cluster. -/
theorem clusterOn_sdiff_eq_of_component_eq_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {R t : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z ∈ U \ K)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R)
    (hK : (K ∩ ball (0 : ℂ) R).Countable) (ht : 0 < t) :
    clusterOn μ (U \ K) z t = cluster μ R z t \ K := by
  have hc := connectedComponentIn_sdiff_of_countable_on_component hU hz (hcomp ▸ hK)
  rw [hcomp] at hc
  exact clusterOn_eq_sdiff_of_component_eq_countable_disc hμ hV hUK
    (hUb.subset sdiff_subset) hR hz hc hK ht

/-- Strong compatibility after such a deletion holds under either
compact-containment alternative. -/
theorem regularizedFamily_strongCompatibility_sdiff_of_component_eq_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {R t : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z ∈ U \ K)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R)
    (hK : (K ∩ ball (0 : ℂ) R).Countable) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U \ K ∨ closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hc := connectedComponentIn_sdiff_of_countable_on_component hU hz (hcomp ▸ hK)
  rw [hcomp] at hc
  exact regularizedFamily_strongCompatibility_of_component_eq_countable_disc
    hμ hV hUK (hUb.subset sdiff_subset) hR hz hc hK ht hΛ hcl


end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.GreenRegularDomainAdmissibility
import HarmonicBalls.Proofs.Sec5.CompactComponentRemoval

/-! # Countable deletion on Green-regular pole components

These results use the potential-theoretic infrastructure of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- Green regularity of the original pole component gives exact deletion. -/
theorem clusterOn_sdiff_of_countable_greenRegular_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0)) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  have hw := leastSupersolutionOn_mem_of_bounded_greenRegular hμ hV
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary
  exact clusterOn_sdiff_of_countable_on_component hμ hV hU hUK hUb ht.le hz hK hw

/-- The deleted cluster has the same closure as the original cluster. -/
theorem closure_clusterOn_sdiff_of_countable_greenRegular_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0)) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  have hw := leastSupersolutionOn_mem_of_bounded_greenRegular hμ hV
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary
  exact closure_clusterOn_sdiff_of_countable_on_component hμ hV hU hUK hUb ht hz hK hw

/-- Two deletions agree away from their union and have the same closure. -/
theorem clusterOn_two_countable_deletions_greenRegular_component
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
        (𝓝[connectedComponentIn U z] y) (𝓝 0)) :
    (clusterOn μ (U \ K) z t \ L = clusterOn μ (U \ L) z t \ K) ∧
    (closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ (U \ L) z t)) := by
  constructor
  · rw [clusterOn_sdiff_of_countable_greenRegular_component hμ hV hU hUK hUb ht hzK hK hboundary,
      clusterOn_sdiff_of_countable_greenRegular_component hμ hV hU hUL hUb ht hzL hL hboundary]
    ext x
    simp only [Set.mem_sdiff]
    tauto
  · exact (closure_clusterOn_sdiff_of_countable_greenRegular_component hμ hV hU hUK hUb ht hzK hK hboundary).trans
      (closure_clusterOn_sdiff_of_countable_greenRegular_component hμ hV hU hUL hUb ht hzL hL hboundary).symm

#print axioms clusterOn_sdiff_of_countable_greenRegular_component
#print axioms closure_clusterOn_sdiff_of_countable_greenRegular_component
#print axioms clusterOn_two_countable_deletions_greenRegular_component

end HarmonicBalls

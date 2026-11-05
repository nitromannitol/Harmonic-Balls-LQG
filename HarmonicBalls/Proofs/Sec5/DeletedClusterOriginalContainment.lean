import HarmonicBalls.Proofs.Sec5.CompactComponentRemoval
import HarmonicBalls.Proofs.Sec5.ComponentRelativeCountableLocality

/-! # Original-domain containment after countable deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- If two measures agree off a relatively countable deletion, containment of
 the deleted-domain cluster in the original domain determines its closure from
 the regularized family. Its closure may meet the deleted set. -/
theorem regularizedFamily_closure_eq_of_deleted_cluster_contained_in_original
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K))
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (clusterOn ν (U \ K) z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn ν (U \ K) z t) := by
  have heqν := clusterOn_sdiff_eq_of_component_restrict_sdiff_relative_countable
    hμ hν hVμ hVν hU hUK hUb hz hK hμν ht.le hw
  have heqμ := clusterOn_sdiff_of_countable_on_component
    hμ hVμ hU hUK hUb ht.le hz hK hw
  have hclosure : closure (clusterOn ν (U \ K) z t) = closure (clusterOn μ U z t) := by
    rw [heqν, ← heqμ]
    exact closure_clusterOn_sdiff_of_countable_on_component hμ hVμ hU hUK hUb ht hz hK hw
  rw [hclosure] at hcl ⊢
  exact regularizedFamily_closure_eq_clusterOn_of_component_compact_containment
    hμ hVμ hU hUb ht hz.1 hw hΛ hcl

#print axioms regularizedFamily_closure_eq_of_deleted_cluster_contained_in_original

end HarmonicBalls

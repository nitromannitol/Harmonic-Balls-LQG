import HarmonicBalls.Proofs.Sec5.GreenRegularCountableDeletion
import HarmonicBalls.Proofs.Sec5.ComponentRelativeCountableLocality
import HarmonicBalls.Proofs.Sec5.RegularizedCountableRemoval
import HarmonicBalls.Proofs.Sec5.DeletedClusterOriginalContainment

/-! # Measure locality for Green-regular countable deletion

These results use the potential-theoretic infrastructure of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- A second measure agreeing away from the deletion yields the original
cluster with the deleted points removed. -/
theorem clusterOn_sdiff_eq_of_restrict_eq_greenRegular_component
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U \ K)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K)) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0)) :
    clusterOn ν (U \ K) z t = clusterOn μ U z t \ K := by
  have hw := leastSupersolutionOn_mem_of_bounded_greenRegular hμ hVμ
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary
  exact clusterOn_sdiff_eq_of_component_restrict_sdiff_relative_countable
    hμ hν hVμ hVν hU hUK hUb hz hK hμν ht.le hw

/-- Under the same locality hypothesis, deletion preserves the cluster closure. -/
theorem closure_clusterOn_sdiff_eq_of_restrict_eq_greenRegular_component
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U \ K)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K)) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0)) :
    closure (clusterOn ν (U \ K) z t) = closure (clusterOn μ U z t) := by
  rw [clusterOn_sdiff_eq_of_restrict_eq_greenRegular_component
    hμ hν hVμ hVν hU hUK hUb hz hK hμν ht hboundary,
    ← clusterOn_sdiff_of_countable_greenRegular_component hμ hVμ hU hUK hUb ht hz hK hboundary]
  exact closure_clusterOn_sdiff_of_countable_greenRegular_component hμ hVμ hU hUK hUb ht hz hK hboundary

/-- A regularized family and the deleted cluster have the same closure when
one of their closures is contained in the original domain. -/
theorem regularizedFamily_closure_eq_deleted_of_restrict_eq_greenRegular
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U \ K)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K)) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn ν (U \ K) z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn ν (U \ K) z t) := by
  rcases hcl with hcl | hcl
  · exact regularizedFamily_closure_eq_sdiff_of_restrict_eq_of_boundary
      hμ hν hVμ hVν hU hUK hUb ht hz hK hμν hboundary hΛ hcl
  · have hw := leastSupersolutionOn_mem_of_bounded_greenRegular hμ hVμ
      hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
      (mem_connectedComponentIn hz.1) ht hboundary
    exact regularizedFamily_closure_eq_of_deleted_cluster_contained_in_original
      hμ hν hVμ hVν hU hUK hUb ht hz hK hμν hw hΛ hcl

/-- The same containment alternatives also determine the regularized family
for the second measure. -/
theorem regularizedFamily_eq_of_restrict_eq_greenRegular_deletion
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U \ K)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K)) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn ν (U \ K) z t) ⊆ U) :
    Λ t = Λ' t := by
  have heq := regularizedFamily_closure_eq_deleted_of_restrict_eq_greenRegular
    hμ hν hVμ hVν hU hUK hUb hz hK hμν ht hboundary hΛ hcl
  have hΛcl : closure (Λ t) ⊆ U := by
    rcases hcl with hcl | hcl
    · exact hcl
    · rw [heq]
      exact hcl
  exact regularizedFamily_eq_of_component_restrict_sdiff_relative_countable
    hμ hν hVμ hVν hU rfl hK hμν ht hΛ hΛ' (Or.inl hΛcl)

#print axioms regularizedFamily_eq_of_restrict_eq_greenRegular_deletion
#print axioms regularizedFamily_closure_eq_deleted_of_restrict_eq_greenRegular
#print axioms clusterOn_sdiff_eq_of_restrict_eq_greenRegular_component
#print axioms closure_clusterOn_sdiff_eq_of_restrict_eq_greenRegular_component

end HarmonicBalls

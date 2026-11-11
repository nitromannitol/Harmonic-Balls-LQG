import HarmonicBalls.Proofs.Sec5.ComponentMeasureLocality
import HarmonicBalls.Proofs.Sec5.CountableDiscCompatibility

/-! # Compatibility for a countably punctured disc component -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- If the pole component is a countably punctured disc, its cluster is the
disc cluster with the deleted points removed, regardless of the other
components of the domain. -/
theorem clusterOn_eq_sdiff_of_component_eq_countable_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ U)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R \ K)
    (hK : (K ∩ ball (0 : ℂ) R).Countable) (ht : 0 < t) :
    clusterOn μ U z t = cluster μ R z t \ K := by
  have hD : IsOpen (ball (0 : ℂ) R \ K) := hcomp ▸ hU.connectedComponentIn
  have hzD : z ∈ ball (0 : ℂ) R \ K := hcomp ▸ mem_connectedComponentIn hz
  rw [clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hU hUb hz ht.le, hcomp]
  exact clusterOn_relative_countable_disc_eq_sdiff hμ hR (hV R hR) K hD hK hzD ht

/-- Strong compatibility holds for a countably punctured disc pole component
under either compact-containment alternative. The least supersolution on the
punctured component is not assumed admissible. -/
theorem regularizedFamily_strongCompatibility_of_component_eq_countable_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ U)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R \ K)
    (hK : (K ∩ ball (0 : ℂ) R).Countable) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  have hD : IsOpen (ball (0 : ℂ) R \ K) := hcomp ▸ hU.connectedComponentIn
  have hzD : z ∈ ball (0 : ℂ) R \ K := hcomp ▸ mem_connectedComponentIn hz
  have hc := clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hU hUb hz ht.le
  have hsmall : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball 0 R \ K := by
    rcases hcl with hcl | hcl
    · left
      rw [← hcomp]
      exact (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
        (subset_closure (hΛ.1.mem t ht)) hcl
    · right
      rw [← hcomp, ← hc]
      exact closure_subset_connectedComponentIn_of_subset hU
        (clusterOn_subset_connectedComponentIn hU hUb hz ht.le) hcl
  have heq := regularizedFamily_strongCompatibility_relative_countable_disc
    hμ hV hR K hD hK hzD ht hΛ hsmall
  rw [hc, hcomp]
  exact heq

/-- For this class of domains, the two compact-containment alternatives are
equivalent. -/
theorem regularizedFamily_containment_iff_of_component_eq_countable_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ U)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R \ K)
    (hK : (K ∩ ball (0 : ℂ) R).Countable) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z) :
    closure (Λ t) ⊆ U ↔ closure (clusterOn μ U z t) ⊆ U := by
  constructor
  · intro hcl
    rw [← regularizedFamily_strongCompatibility_of_component_eq_countable_disc
      hμ hV hU hUb hR hz hcomp hK ht hΛ (Or.inl hcl)]
    exact hcl
  · intro hcl
    rw [regularizedFamily_strongCompatibility_of_component_eq_countable_disc
      hμ hV hU hUb hR hz hcomp hK ht hΛ (Or.inr hcl)]
    exact hcl


end HarmonicBalls

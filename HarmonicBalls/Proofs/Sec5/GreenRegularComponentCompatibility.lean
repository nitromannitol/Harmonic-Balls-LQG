import HarmonicBalls.Proofs.Sec5.ComponentAdmissibility
import HarmonicBalls.Proofs.Sec5.ComponentMeasureLocality
import HarmonicBalls.Proofs.Sec5.GreenRegularDomainAdmissibility

/-! # Compatibility for a disc pole component

This restricted consequence uses the potential-theoretic infrastructure of
Leonardo Bonanno. The Green-regular component result keeps the boundary limits explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- A disc pole component supplies the admissibility needed for strong
compatibility; the Green boundary limit is retained explicitly. -/
theorem regularizedFamily_strongCompatibility_of_disc_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hcomp : connectedComponentIn U z = ball (0 : ℂ) R)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z → Tendsto
        (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  have hVc : IsOpen (connectedComponentIn U z) := hU.connectedComponentIn
  have hVb := hUb.subset (connectedComponentIn_subset U z)
  have hzV := mem_connectedComponentIn hz
  have hcomp' : connectedComponentIn (connectedComponentIn U z) z = ball (0 : ℂ) R := by
    apply subset_antisymm
    · exact (connectedComponentIn_subset _ _).trans (by rw [hcomp])
    · apply (isPreconnected_ball : IsPreconnected (ball (0 : ℂ) R)).subset_connectedComponentIn
      · rw [← hcomp]; exact hzV
      · rw [hcomp]
  have hv := leastSupersolutionOn_mem_of_connectedComponentIn_eq_ball
    hμ hVc hVb hR (hV R hR) hzV hcomp' ht
  exact regularizedFamily_strongCompatibility_of_component_boundary hU hUb hz ht
    hv hboundary hΛ hopen hcl

/-- Strong compatibility for a Green-regular pole component, with the
compact containment and openness hypotheses of the comparison theorem. -/
theorem regularizedFamily_strongCompatibility_of_greenRegular_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z → Tendsto
        (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  obtain ⟨R, hRsub⟩ := hUb.subset_ball (0 : ℂ)
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (mem_ball.mp (hRsub hz))
  have hv := leastSupersolutionOn_mem_of_greenRegular hμ hR (hV R hR)
    hU.connectedComponentIn ((connectedComponentIn_subset U z).trans hRsub)
    (mem_connectedComponentIn hz) ht hboundary
  exact regularizedFamily_strongCompatibility_of_component_boundary hU hUb hz ht
    hv hboundary hΛ hopen hcl

#print axioms regularizedFamily_strongCompatibility_of_greenRegular_component

#print axioms regularizedFamily_strongCompatibility_of_disc_component

end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.CompactOriginalExactRemoval
import HarmonicBalls.Proofs.Sec5.ComponentRelativeCountableLocality

/-! # Countable removal on a compactly contained time interval -/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- Compact containment at a terminal time gives exact removal and closure
compatibility at every earlier positive time, including for a second measure
which agrees away from the relatively countable deletion. -/
theorem clusterOn_countable_removal_interval_of_compact_regularizedFamily
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {T : ℝ} {z : ℂ} (hT : 0 < T)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K))
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ T) ⊆ U) :
    ∀ t ∈ Ioc (0 : ℝ) T,
      clusterOn ν (U \ K) z t = clusterOn μ U z t \ K ∧
      closure (Λ t) = closure (clusterOn ν (U \ K) z t) := by
  intro t ht
  have hclt : closure (Λ t) ⊆ U :=
    (closure_mono (hΛ.1.monotoneOn ht.1 hT ht.2)).trans hcl
  have hclC : closure (Λ t) ⊆ connectedComponentIn U z :=
    (hΛ.1.isConnected t ht.1).isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (hΛ.1.mem t ht.1)) hclt
  have hw := leastSupersolutionOn_mem_of_compact_regularizedFamily hμ hVμ
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht.1 hboundary hΛ hclC
  exact ⟨clusterOn_sdiff_eq_of_component_restrict_sdiff_relative_countable
      hμ hν hVμ hVν hU hUK hUb hz hK hμν ht.1.le hw,
    regularizedFamily_closure_eq_sdiff_of_restrict_eq_of_boundary
      hμ hν hVμ hVν hU hUK hUb ht.1 hz hK hμν hboundary hΛ hclt⟩


end HarmonicBalls

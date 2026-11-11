import HarmonicBalls.Proofs.Sec5.CompactRegularizedComponent
import HarmonicBalls.Proofs.Sec5.CompactComponentRemoval
import HarmonicBalls.Proofs.Sec5.ComponentRelativeCountableLocality

/-! # Countable removal for compact regularized clusters -/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- A relatively countable deletion preserves the closure of a regularized
cluster compactly contained in the original domain. The deleted set may meet
the cluster; no least-supersolution admissibility is assumed. -/
theorem regularizedFamily_closure_eq_sdiff_of_compact_original_of_boundary
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
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hclC : closure (Λ t) ⊆ connectedComponentIn U z :=
    (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (hΛ.1.mem t ht)) hcl
  have hw := leastSupersolutionOn_mem_of_compact_regularizedFamily hμ hV
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary hΛ hclC
  have heq := regularizedFamily_closure_eq_clusterOn_of_boundary_of_volumeGrowth
    hμ hV hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary hΛ hclC
  rw [← clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hU hUb hz.1 ht.le] at heq
  rw [closure_clusterOn_sdiff_of_countable_on_component hμ hV hU hUK hUb ht hz hK hw]
  exact heq

/-- The same conclusion holds for a second measure agreeing with the first
away from the relatively countable deleted set on the pole component. -/
theorem regularizedFamily_closure_eq_sdiff_of_restrict_eq_of_boundary
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K))
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    closure (Λ t) = closure (clusterOn ν (U \ K) z t) := by
  have hclC : closure (Λ t) ⊆ connectedComponentIn U z :=
    (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (hΛ.1.mem t ht)) hcl
  have hw := leastSupersolutionOn_mem_of_compact_regularizedFamily hμ hVμ
    hU.connectedComponentIn (hUb.subset (connectedComponentIn_subset U z))
    (mem_connectedComponentIn hz.1) ht hboundary hΛ hclC
  have heq := clusterOn_sdiff_eq_of_component_restrict_sdiff_relative_countable
    hμ hν hVμ hVν hU hUK hUb hz hK hμν ht.le hw
  have heqμ := clusterOn_sdiff_eq_of_component_restrict_sdiff_relative_countable
    hμ hμ hVμ hVμ hU hUK hUb hz hK rfl ht.le hw
  rw [heq, ← heqμ]
  exact regularizedFamily_closure_eq_sdiff_of_compact_original_of_boundary
    hμ hVμ hU hUK hUb ht hz hK hboundary hΛ hcl

/-- In a pole component given by an intersection of discs, Green boundary
regularity follows from the supporting discs. -/
theorem regularizedFamily_closure_eq_sdiff_of_compact_original_of_disc_intersection
    {ι : Type*} {c : ι → ℂ} {r : ι → ℝ}
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hcomp : connectedComponentIn U z = ⋂ i, ball (c i) (r i))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) :=
  regularizedFamily_closure_eq_sdiff_of_compact_original_of_boundary
    hμ hV hU hUK hUb ht hz hK
    (tendsto_greenFunction_zero_of_enclosing_discs (mem_connectedComponentIn hz.1)
      (exists_enclosing_disc_of_eq_iInter_ball hcomp)) hΛ hcl

/-- Agreement of circle averages on compact subsets away from a relatively
countable deletion determines the deleted-domain cluster closure. -/
theorem IsLQGLimit.regularizedFamily_closure_eq_sdiff_of_boundary
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hD : IsOpen (connectedComponentIn U z \ K))
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ connectedComponentIn U z \ K →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    closure (Λ t) = closure (clusterOn ν (U \ K) z t) :=
  regularizedFamily_closure_eq_sdiff_of_restrict_eq_of_boundary
    hμ hν hVμ hVν hU hUK hUb ht hz hK (hμlim.restrict_eq hνlim hD hloc)
    hboundary hΛ hcl

end HarmonicBalls

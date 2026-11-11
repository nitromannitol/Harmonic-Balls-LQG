import HarmonicBalls.Proofs.Sec5.RelativeCountableMeasureLocality
import HarmonicBalls.Proofs.Sec5.ComponentMeasureLocality
import HarmonicBalls.Proofs.Sec5.ComponentwiseRemovalCompatibility

/-! # Locality outside countable subsets of the pole component -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Two bounded open domains with the same pole component have identical
clusters when their measures agree off a relatively countable subset of that
component. Neither least supersolution is assumed admissible. -/
theorem clusterOn_eq_of_component_restrict_sdiff_relative_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U V K : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    {z : ℂ} (hzU : z ∈ U) (hzV : z ∈ V)
    (hcomp : connectedComponentIn U z = connectedComponentIn V z)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K)) {t : ℝ} (ht : 0 ≤ t) :
    clusterOn μ U z t = clusterOn ν V z t :=
  clusterOn_eq_of_connectedComponentIn_eq_of_restrict_eq hμ hν hVμ hVν hU hV
    hUb hVb hzU hzV hcomp
    (restrict_eq_of_restrict_sdiff_relative_countable hVμ hVν hK hμν) ht

/-- After a relatively countable deletion, the cluster for another measure
agreeing off the deletion is the original cluster with those points removed.
Only the original measure's pole-component least supersolution is assumed
admissible; no admissibility on the deleted domain is needed. -/
theorem clusterOn_sdiff_eq_of_component_restrict_sdiff_relative_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U \ K)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K)) {t : ℝ} (ht : 0 ≤ t)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    clusterOn ν (U \ K) z t = clusterOn μ U z t \ K := by
  have hfull := restrict_eq_of_restrict_sdiff_relative_countable hVμ hVν hK hμν
  have hsuper := supersolutionsOn_eq_of_restrict_eq hU.connectedComponentIn.measurableSet
    hfull z t
  have hleast : leastSupersolutionOn μ (connectedComponentIn U z) z t =
      leastSupersolutionOn ν (connectedComponentIn U z) z t := by
    funext x
    unfold leastSupersolutionOn
    rw [hsuper]
  have hwν : leastSupersolutionOn ν (connectedComponentIn U z) z t ∈
      supersolutionsOn ν (connectedComponentIn U z) z t := by
    rw [← hleast, ← hsuper]
    exact hw
  rw [clusterOn_sdiff_of_countable_on_component hν hVν hU hUK hUb ht hz hK hwν]
  rw [← clusterOn_eq_of_connectedComponentIn_eq_of_restrict_eq hμ hν hVμ hVν
    hU hU hUb hUb hz.1 hz.1 rfl hfull ht]

/-- A regularized cluster compactly contained in either domain depends only
on the measure away from a relatively countable subset of their common pole
component. The exceptional set may contain the pole or meet the cluster. -/
theorem regularizedFamily_eq_of_component_restrict_sdiff_relative_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U V K : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hcomp : connectedComponentIn U z = connectedComponentIn V z)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K)) {t : ℝ} (ht : 0 < t)
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (Λ' t) ⊆ V) : Λ t = Λ' t := by
  apply regularizedFamily_eq_of_restrict_sdiff_relative_countable hμ hν hVμ hVν
    hU.connectedComponentIn hK hμν ht hΛ hΛ'
  rcases hcl with hcl | hcl
  · left
    exact (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (hΛ.1.mem t ht)) hcl
  · right
    rw [hcomp]
    exact (hΛ'.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
      (subset_closure (hΛ'.1.mem t ht)) hcl

/-- Local agreement of circle averages away from a relatively countable
subset of the common pole component determines the general-domain cluster. -/
theorem IsLQGLimit.clusterOn_eq_of_component_relative_countable
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U V K : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    {z : ℂ} (hzU : z ∈ U) (hzV : z ∈ V)
    (hcomp : connectedComponentIn U z = connectedComponentIn V z)
    (hD : IsOpen (connectedComponentIn U z \ K))
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ connectedComponentIn U z \ K →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x)
    {t : ℝ} (ht : 0 ≤ t) : clusterOn μ U z t = clusterOn ν V z t :=
  clusterOn_eq_of_component_restrict_sdiff_relative_countable hμ hν hVμ hVν hU hV
    hUb hVb hzU hzV hcomp hK (hμlim.restrict_eq hνlim hD hloc) ht

/-- The same circle-average locality determines regularized families under
compact containment in either of the two domains. -/
theorem IsLQGLimit.regularizedFamily_eq_of_component_relative_countable
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U V K : Set ℂ} (hU : IsOpen U) {z : ℂ}
    (hcomp : connectedComponentIn U z = connectedComponentIn V z)
    (hD : IsOpen (connectedComponentIn U z \ K))
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ connectedComponentIn U z \ K →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x)
    {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (Λ' t) ⊆ V) : Λ t = Λ' t :=
  regularizedFamily_eq_of_component_restrict_sdiff_relative_countable hμ hν hVμ hVν
    hU hcomp hK (hμlim.restrict_eq hνlim hD hloc) ht hΛ hΛ' hcl


end HarmonicBalls

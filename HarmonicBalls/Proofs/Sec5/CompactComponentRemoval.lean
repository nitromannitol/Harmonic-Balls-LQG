import HarmonicBalls.Proofs.Sec5.GeneralDomainClusterOpen
import HarmonicBalls.Proofs.Sec5.RelativeCountableMeasureLocality

/-! # Compact component removal for regularized clusters

Deleting a relatively countable set from the pole component preserves the closure of the cluster when its least supersolution is admissible (`closure_clusterOn_sdiff_of_countable_on_component`). Under compact containment in the original domain, `regularizedFamily_closure_eq_clusterOn_of_component_compact_containment` and `regularizedFamily_closure_eq_sdiff_of_component_compact_containment` identify the closure of the regularized cluster family with the closure of the cluster before and after the deletion. Under the same hypotheses, `regularizedFamily_eq_of_restrict_sdiff_component_compact_containment` shows that two regularized cluster families whose measures agree off the deleted set coincide at time `t`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Deleting a relatively countable set from the pole component preserves
the closure of the cluster when its least supersolution is admissible. -/
theorem closure_clusterOn_sdiff_of_countable_on_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  rw [clusterOn_sdiff_of_countable_on_component hμ hV hU hUK hUb ht.le hz hK hw]
  have hc := clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hU hUb hz.1 ht.le
  have hopen : IsOpen (clusterOn μ U z t) := by
    rw [hc]
    exact isOpen_clusterOn_of_leastSupersolutionOn_mem hU.connectedComponentIn
      (hUb.subset (connectedComponentIn_subset U z)) (mem_connectedComponentIn hz.1) ht hw
  apply closure_sdiff_countable_inter hopen
  exact hK.mono (by
    intro x hx
    exact ⟨hx.1, clusterOn_subset_connectedComponentIn hU hUb hz.1 ht.le hx.2⟩)

/-- An admissible pole-component cluster which is compactly contained in
the original domain determines the regularized family's closure. -/
theorem regularizedFamily_closure_eq_clusterOn_of_component_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {t : ℝ} {z : ℂ} (ht : 0 < t) (hz : z ∈ U)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  have hCb := hUb.subset (connectedComponentIn_subset U z)
  have hzC := mem_connectedComponentIn hz
  have hc := clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hU hUb hz ht.le
  have hsmall : closure (clusterOn μ (connectedComponentIn U z) z t) ⊆
      connectedComponentIn U z := by
    rw [← hc]
    exact closure_subset_connectedComponentIn_of_subset hU
      (clusterOn_subset_connectedComponentIn hU hUb hz ht.le) hcl
  obtain ⟨r, hr⟩ := hCb.subset_ball (0 : ℂ)
  have hrpos : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp (hr hzC))
  have heq := clusterOn_eq_cluster_of_compact_containment hU.connectedComponentIn
    hr hzC ht hw hsmall
  have hdisc : closure (cluster μ r z t) ⊆ ball (0 : ℂ) r := by
    rw [← heq]
    exact hsmall.trans hr
  have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hrpos (hV r hrpos) (hr hzC) ht).2.2
  rw [hc, heq]
  exact regularizedFamily_closure_eq_discCluster_of_compact_containment hrpos (hr hzC) ht hΛ
    (isOpen_cluster_of_volumeGrowth hμ hV ht) hv hdisc

/-- Compatibility after deletion follows from compact containment in the
original domain, even if the deleted set meets the cluster closure. -/
theorem regularizedFamily_closure_eq_sdiff_of_component_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  rw [closure_clusterOn_sdiff_of_countable_on_component hμ hV hU hUK hUb ht hz hK hw]
  exact regularizedFamily_closure_eq_clusterOn_of_component_compact_containment
    hμ hV hU hUb ht hz.1 hw hΛ hcl

/-- Agreement off a relatively countable set on the pole component determines
the regularized cluster under compact containment in the original domain. -/
theorem regularizedFamily_eq_of_restrict_sdiff_component_compact_containment
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {t : ℝ} {z : ℂ} (ht : 0 < t) (hz : z ∈ U)
    (hK : (K ∩ connectedComponentIn U z).Countable)
    (hμν : μ.restrict (connectedComponentIn U z \ K) =
      ν.restrict (connectedComponentIn U z \ K))
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (clusterOn μ U z t) ⊆ U) : Λ t = Λ' t := by
  have heq := regularizedFamily_closure_eq_clusterOn_of_component_compact_containment
    hμ hVμ hU hUb ht hz hw hΛ hcl
  have hinside : closure (Λ t) ⊆ connectedComponentIn U z := by
    rw [heq]
    exact closure_subset_connectedComponentIn_of_subset hU
      (clusterOn_subset_connectedComponentIn hU hUb hz ht.le) hcl
  exact regularizedFamily_eq_of_restrict_sdiff_relative_countable hμ hν hVμ hVν
    hU.connectedComponentIn hK hμν ht hΛ hΛ' (Or.inl hinside)


end HarmonicBalls

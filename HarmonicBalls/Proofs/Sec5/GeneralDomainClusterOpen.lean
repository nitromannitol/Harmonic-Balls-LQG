import HarmonicBalls.Proofs.Sec5.ComponentwiseRemovalCompatibility
import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity

/-! # Openness of general-domain clusters -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- An admissible least supersolution gives an open cluster on any bounded
open planar domain. At the pole, the Green singularity supplies a whole
neighborhood of the pole in the cluster. -/
theorem isOpen_clusterOn_of_leastSupersolutionOn_mem
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    IsOpen (clusterOn μ U z t) := by
  obtain ⟨R, hUR⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨h, hh, hG⟩ := exists_harmonicOnNhd_greenFunction_difference hU hUb hUR hz
  have hvcont : ∀ x ∈ U, ContinuousAt (leastSupersolutionOn μ U z t) x := by
    intro x hx
    exact hv.1.continuousAt (mem_of_superset (hU.mem_nhds hx) subset_closure)
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxz : x = z
  · subst x
    have hvnear : ∀ᶠ y in 𝓝 z,
        leastSupersolutionOn μ U z t z - 1 < leastSupersolutionOn μ U z t y :=
      (hvcont z hz).eventually (Ioi_mem_nhds (by linarith))
    have hhnear : ∀ᶠ y in 𝓝 z, h z - 1 < h y :=
      ((hh z hz).1.continuousAt).eventually (Ioi_mem_nhds (by linarith))
    have hnear : ∀ᶠ y in 𝓝[≠] z,
        (1 - leastSupersolutionOn μ U z t z - t * (h z - 1)) / t <
          greenFunction (ball (0 : ℂ) R) z y :=
      (tendsto_greenFunction_ball_pole (hUR hz)).eventually (eventually_gt_atTop _)
    rw [eventually_nhdsWithin_iff] at hnear
    filter_upwards [hU.mem_nhds hz, hvnear, hhnear, hnear] with y hy hyv hyh hyG
    refine ⟨hy, ?_⟩
    by_cases hyz : y = z
    · exact Or.inl hyz
    · right
      have hineq := (div_lt_iff₀ ht).mp (hyG hyz)
      have heq := hG y hy hyz
      nlinarith
  · have hGcont : ContinuousAt (greenFunction U z) x := by
      have hc := ((hh x hx.1).1.continuousAt).add
        ((continuousOn_greenFunction_ball (hUR hz)).continuousAt
          (isOpen_compl_singleton.mem_nhds hxz))
      apply hc.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx.1, isOpen_compl_singleton.mem_nhds hxz] with y hy hyz
      have heq := hG y hy hyz
      change greenFunction U z y = h y + greenFunction (ball 0 R) z y
      linarith
    have hlt : -t * greenFunction U z x < leastSupersolutionOn μ U z t x :=
      hx.2.resolve_left hxz
    filter_upwards [hU.mem_nhds hx.1,
      (hGcont.const_mul (-t)).eventually_lt (hvcont x hx.1) hlt] with y hy hlt'
    exact ⟨hy, Or.inr hlt'⟩

/-- Under volume growth, all disc clusters containing the pole are open. -/
theorem isOpen_cluster_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {z : ℂ} {t : ℝ} (ht : 0 < t) :
    ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t) := by
  intro r hr hz
  rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hV r hr) z hz t ht).2.2.1]
  exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
    hμ hr (hV r hr) hz ht

/-- Compact containment gives compatibility after componentwise countable
deletion, with openness supplied by admissibility and volume growth. -/
theorem regularizedFamily_closure_eq_of_countable_on_component_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  exact regularizedFamily_closure_eq_of_countable_on_component hμ hV hU hUK hUb ht hz hK hw
    (isOpen_clusterOn_of_leastSupersolutionOn_mem hU.connectedComponentIn
      (hUb.subset (connectedComponentIn_subset U z)) (mem_connectedComponentIn hz.1) ht hw)
    hΛ (isOpen_cluster_of_volumeGrowth hμ hV ht) hcl

/-- If the original pole component also has Green boundary regularity, either
compact-containment alternative gives compatibility after deletion. -/
theorem regularizedFamily_strongCompatibility_of_countable_on_component_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  exact regularizedFamily_strongCompatibility_of_countable_on_component hμ hV hU hUK hUb ht hz
    hK hw (isOpen_clusterOn_of_leastSupersolutionOn_mem hU.connectedComponentIn
      (hUb.subset (connectedComponentIn_subset U z)) (mem_connectedComponentIn hz.1) ht hw)
    hboundary hΛ (isOpen_cluster_of_volumeGrowth hμ hV ht) hcl

#print axioms isOpen_clusterOn_of_leastSupersolutionOn_mem
#print axioms isOpen_cluster_of_volumeGrowth
#print axioms regularizedFamily_closure_eq_of_countable_on_component_of_volumeGrowth
#print axioms regularizedFamily_strongCompatibility_of_countable_on_component_of_volumeGrowth

end HarmonicBalls

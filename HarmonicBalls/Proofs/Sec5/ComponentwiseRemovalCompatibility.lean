import HarmonicBalls.Proofs.Sec5.ComponentwiseCountableDeletion

/-! # Countable removal from an arbitrary pole component -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- The pole component of an open domain remains open after a deletion that
is relatively closed in the domain. -/
theorem isOpen_component_sdiff {U K : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hUK : IsOpen (U \ K)) :
    IsOpen (connectedComponentIn U z \ K) := by
  have heq : connectedComponentIn U z \ K = connectedComponentIn U z ∩ (U \ K) := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨hx, connectedComponentIn_subset U z hx, hxK⟩
    · rintro ⟨hx, _, hxK⟩
      exact ⟨hx, hxK⟩
  rw [heq]
  exact hU.connectedComponentIn.inter hUK

/-- Volume growth gives a continuous measure potential on each bounded set. -/
theorem exists_continuous_potential_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U) :
    ∃ q : ℂ → ℝ, ContinuousOn q U ∧ HasLaplacian q 0 μ U := by
  obtain ⟨R, hUR⟩ := hUb.subset_ball (0 : ℂ)
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (mem_ball.mp (hUR hz))
  exact ⟨greenPotentialBall μ R,
    (greenPotentialBallContinuousStep_holds μ hμ R βm βp hR (hV R hR)).mono
      (hUR.trans ball_subset_closedBall),
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR (hV R hR)).mono_domain hUR⟩

/-- Countable deletion on the pole component removes exactly those points
from the cluster. The deletion may be arbitrary on the other components. -/
theorem clusterOn_sdiff_of_countable_on_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 ≤ t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  have hCb := hUb.subset (connectedComponentIn_subset U z)
  obtain ⟨q, hqc, hq⟩ := exists_continuous_potential_of_volumeGrowth hμ hV hCb
    (mem_connectedComponentIn hz.1)
  obtain ⟨R, hR⟩ := hCb.closure.subset_ball (0 : ℂ)
  have hcomp := connectedComponentIn_sdiff_of_countable_on_component hU hz hK
  rw [clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hUK
      (hUb.subset sdiff_subset) hz ht, hcomp,
    clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hU hUb hz.1 ht]
  exact clusterOn_sdiff_of_relative_countable hμ hU.connectedComponentIn hCb hR
    (isOpen_component_sdiff hU hUK) hK hqc hq ht
    ⟨mem_connectedComponentIn hz.1, hz.2⟩ hw

/-- Compact containment of the deleted-domain cluster gives compatibility
without any boundary regularity assumption on the original component. -/
theorem regularizedFamily_closure_eq_of_countable_on_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    (hopenU : IsOpen (clusterOn μ (connectedComponentIn U z) z t))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hCb := hUb.subset (connectedComponentIn_subset U z)
  obtain ⟨q, hqc, hq⟩ := exists_continuous_potential_of_volumeGrowth hμ hV hCb
    (mem_connectedComponentIn hz.1)
  obtain ⟨R, hR⟩ := hCb.closure.subset_ball (0 : ℂ)
  have hcomp := connectedComponentIn_sdiff_of_countable_on_component hU hz hK
  have heq := clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hUK
    (hUb.subset sdiff_subset) hz ht.le
  rw [hcomp] at heq
  have hsmall : closure (clusterOn μ (connectedComponentIn U z \ K) z t) ⊆
      connectedComponentIn U z \ K := by
    rw [← heq, ← hcomp]
    exact closure_subset_connectedComponentIn_of_subset hUK
      (clusterOn_subset_connectedComponentIn hUK (hUb.subset sdiff_subset) hz ht.le) hcl
  rw [heq]
  exact regularizedFamily_closure_eq_clusterOn_sdiff_of_relative_countable
    hμ hU.connectedComponentIn hCb hR (isOpen_component_sdiff hU hUK) hK hqc hq ht
    ⟨mem_connectedComponentIn hz.1, hz.2⟩ hw hopenU hΛ hopen hsmall

/-- With Green boundary regularity of the original pole component, either
compact-containment alternative yields strong compatibility after deletion. -/
theorem regularizedFamily_strongCompatibility_of_countable_on_component
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    (hopenU : IsOpen (clusterOn μ (connectedComponentIn U z) z t))
    (hboundary : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      Tendsto (greenFunction (connectedComponentIn U z) z)
        (𝓝[connectedComponentIn U z] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  rcases hcl with hcl | hcl
  · have hCb := hUb.subset (connectedComponentIn_subset U z)
    obtain ⟨q, hqc, hq⟩ := exists_continuous_potential_of_volumeGrowth hμ hV hCb
      (mem_connectedComponentIn hz.1)
    obtain ⟨R, hR⟩ := hCb.closure.subset_ball (0 : ℂ)
    have hcomp := connectedComponentIn_sdiff_of_countable_on_component hU hz hK
    have heq := clusterOn_eq_connectedComponentIn_of_volumeGrowth hμ hV hUK
      (hUb.subset sdiff_subset) hz ht.le
    rw [hcomp] at heq
    have hsmall : closure (Λ t) ⊆ connectedComponentIn U z \ K := by
      rw [← hcomp]
      exact (hΛ.1.isConnected t ht).isPreconnected.closure.subset_connectedComponentIn
        (subset_closure (hΛ.1.mem t ht)) hcl
    rw [heq]
    exact regularizedFamily_strongCompatibility_sdiff_of_relative_countable
      hμ hU.connectedComponentIn hCb hR (isOpen_component_sdiff hU hUK) hK hqc hq ht
      ⟨mem_connectedComponentIn hz.1, hz.2⟩ hw hopenU hboundary hΛ hopen (Or.inl hsmall)
  · exact regularizedFamily_closure_eq_of_countable_on_component
      hμ hV hU hUK hUb ht hz hK hw hopenU hΛ hopen hcl


end HarmonicBalls

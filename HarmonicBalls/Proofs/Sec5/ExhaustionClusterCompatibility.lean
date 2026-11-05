import HarmonicBalls.Proofs.Sec5.GreenRegularExhaustion
import HarmonicBalls.Proofs.Sec5.ExhaustionHorizon
import HarmonicBalls.Proofs.Sec5.MinimumLaplacianGluing
import HarmonicBalls.Proofs.Sec5.CountableDiscCompatibility

/-! # Exhaustion comparison for regularized clusters

The Green-function and obstacle arguments use the potential-theoretic
infrastructure of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- Every cluster in a relatively compact regular exhaustion is contained in
 the cluster of the union, even if the union is not Green-regular. -/
theorem iUnion_clusterOn_subset_of_regular_exhaustion
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n))
    (hsub : ∀ n, closure (V n) ⊆ U) {z : ℂ} (hz : ∀ n, z ∈ V n)
    {t : ℝ} (ht : 0 ≤ t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0)) :
    (⋃ n, clusterOn μ (V n) z t) ⊆ clusterOn μ U z t := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact clusterOn_subset_of_compactly_contained_regular (hopen n) hU hUb
    (hsub n) (hz n) ht (hboundary n) hn

/-- If a regularized cluster is compactly contained in the union of an
increasing regular exhaustion, the closures of the exhausting-domain clusters
are eventually exactly its closure. -/
theorem eventually_closure_clusterOn_eq_regularized_of_exhaustion
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    ∀ᶠ n in atTop, closure (Λ t) = closure (clusterOn μ (V n) z t) := by
  have hcompact : IsCompact (closure (Λ t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, (hΛ.1.isBounded t ht).closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion hcompact hopen hmono (hcover ▸ hcl)
  filter_upwards [eventually_ge_atTop N] with n hn
  exact regularizedFamily_closure_eq_clusterOn_of_boundary_of_volumeGrowth
    hμ hvol (hopen n) (hUb.subset (subset_closure.trans (hsub n)))
    (hz n) ht (hboundary n) hΛ (hN.trans (hmono hn))

/-- Under the regularized-family compact-containment alternative, its closure
is contained in the limiting-domain cluster closure. The converse is not
asserted by the exhaustion comparison. -/
theorem regularized_closure_subset_clusterOn_of_regular_exhaustion
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    closure (Λ t) ⊆ closure (clusterOn μ U z t) := by
  obtain ⟨n, hn⟩ := (eventually_closure_clusterOn_eq_regularized_of_exhaustion
    hμ hvol hUb V hopen hmono hcover hsub hz ht hboundary hΛ hcl).exists
  rw [hn]
  exact closure_mono (clusterOn_subset_of_compactly_contained_regular
    (hopen n) hU hUb (hsub n) (hz n) ht.le (hboundary n))

/-- If the limiting-domain cluster is compactly contained, the exhausting
clusters eventually stabilize to the cluster of any fixed enclosing disc.
This does not identify that stable cluster with the limiting-domain cluster. -/
theorem eventually_clusterOn_eq_enclosing_disc_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = U) (hsub : ∀ n, closure (V n) ⊆ U)
    {z : ℂ} (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    {r : ℝ} (hr : U ⊆ ball (0 : ℂ) r) :
    ∀ᶠ n in atTop, clusterOn μ (V n) z t = cluster μ r z t := by
  have hclusterb : Bornology.IsBounded (clusterOn μ U z t) :=
    hUb.subset (fun _ hx => hx.1)
  have hcompact : IsCompact (closure (clusterOn μ U z t)) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hclusterb.closure⟩
  obtain ⟨N, hN⟩ := HarmonicBalls.IsCompact.subset_monotone_open_iUnion
    hcompact hopen hmono (hcover ▸ hcl)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hVb : Bornology.IsBounded (V n) :=
    hUb.subset (subset_closure.trans (hsub n))
  have hv := leastSupersolutionOn_mem_of_bounded_greenRegular
    hμ hvol (hopen n) hVb (hz n) ht (hboundary n)
  have hsmall : closure (clusterOn μ (V n) z t) ⊆ V n :=
    (closure_mono (clusterOn_subset_of_compactly_contained_regular
      (hopen n) hU hUb (hsub n) (hz n) ht.le (hboundary n))).trans
      (hN.trans (hmono hn))
  exact clusterOn_eq_cluster_of_compact_containment (hopen n)
    (subset_closure.trans ((hsub n).trans hr)) (hz n) ht hv hsmall

/-- For a relatively countable deletion from a disc, compact containment of
its cluster makes the exhaustion clusters eventually equal it as sets. -/
theorem eventually_clusterOn_eq_countable_deleted_disc_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {R : ℝ} (hR : 0 < R) {z : ℂ} (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = ball (0 : ℂ) R \ K)
    (hsub : ∀ n, closure (V n) ⊆ ball (0 : ℂ) R \ K)
    (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆
      ball (0 : ℂ) R \ K) :
    ∀ᶠ n in atTop, clusterOn μ (V n) z t =
      clusterOn μ (ball (0 : ℂ) R \ K) z t := by
  have hzU := hsub 0 (subset_closure (hz 0))
  have hclosure := closure_clusterOn_relative_countable_disc_eq hμ hR (hvol R hR) K hD hK hzU ht
  have hdisj : Disjoint (cluster μ R z t) K := by
    apply disjoint_left.mpr
    intro x hx hKx
    have hxU := hcl (hclosure.symm ▸ subset_closure hx)
    exact hxU.2 hKx
  have heq : clusterOn μ (ball (0 : ℂ) R \ K) z t = cluster μ R z t := by
    rw [clusterOn_relative_countable_disc_eq_sdiff hμ hR (hvol R hR) K hD hK hzU ht]
    exact sdiff_eq_left.mpr hdisj
  have hstable := eventually_clusterOn_eq_enclosing_disc_of_compact_containment
    hμ hvol hD (isBounded_ball.subset sdiff_subset)
    V hopen hmono hcover hsub hz ht hboundary hcl sdiff_subset
  filter_upwards [hstable] with n hn
  exact hn.trans heq.symm

#print axioms eventually_clusterOn_eq_countable_deleted_disc_of_compact_containment

/-- For a punctured disc, compact containment of the limiting cluster makes
regular exhaustion clusters eventually equal that cluster as sets. The proof
does not require the punctured-domain infimum to be admissible. -/
theorem eventually_clusterOn_eq_punctured_disc_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hvol : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {R : ℝ} (hR : 0 < R) {z a : ℂ}
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hcover : (⋃ n, V n) = ball (0 : ℂ) R \ {a})
    (hsub : ∀ n, closure (V n) ⊆ ball (0 : ℂ) R \ {a})
    (hz : ∀ n, z ∈ V n) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) ⊆
      ball (0 : ℂ) R \ {a}) :
    ∀ᶠ n in atTop, clusterOn μ (V n) z t =
      clusterOn μ (ball (0 : ℂ) R \ {a}) z t := by
  exact eventually_clusterOn_eq_countable_deleted_disc_of_compact_containment
    hμ hvol hR {a} (isOpen_ball.sdiff isClosed_singleton)
    (Set.Countable.mono inter_subset_left (Set.countable_singleton a))
    V hopen hmono hcover hsub hz ht hboundary hcl

#print axioms eventually_clusterOn_eq_punctured_disc_of_compact_containment

#print axioms eventually_clusterOn_eq_enclosing_disc_of_compact_containment
#print axioms iUnion_clusterOn_subset_of_regular_exhaustion
#print axioms eventually_closure_clusterOn_eq_regularized_of_exhaustion
#print axioms regularized_closure_subset_clusterOn_of_regular_exhaustion

end HarmonicBalls

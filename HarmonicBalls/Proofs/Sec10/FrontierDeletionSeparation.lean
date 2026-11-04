import HarmonicBalls.Proofs.Sec10.FrontierMinimalSeparation

/-! # Separation by complementary frontiers

A complementary frontier separates its two adjacent domains, but removing any
nonempty subset of that frontier joins those domains in a single component.
The removed subset need not be relatively open or closed.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- For two connected open sets with the stated frontier inclusion, a subset of
the complementary frontier joins the two sets precisely when it is nonempty. -/
theorem mem_connectedComponentIn_compl_frontier_sdiff_iff
    {G U S : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) (hS : S ⊆ frontier U)
    {x y : ℂ} (hx : x ∈ G) (hy : y ∈ U) :
    y ∈ connectedComponentIn (frontier U \ S)ᶜ x ↔ S.Nonempty := by
  constructor
  · intro hxy
    by_contra hn
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hsep := (frontier_minimal_closed_separator hGo hGc hUo hUc hdis hfront hx hy).1
    apply hsep
    simpa [hSempty] using hxy
  · intro hne
    have hsG : S ⊆ closure G := hS.trans (hfront.trans frontier_subset_closure)
    have hsU : S ⊆ closure U := hS.trans frontier_subset_closure
    have hGS : IsPreconnected (G ∪ S) :=
      hGc.isPreconnected.subset_closure subset_union_left (union_subset subset_closure hsG)
    have hUS : IsPreconnected (U ∪ S) :=
      hUc.isPreconnected.subset_closure subset_union_left (union_subset subset_closure hsU)
    obtain ⟨a, ha⟩ := hne
    have hmeet : ((G ∪ S) ∩ (U ∪ S)).Nonempty := ⟨a, Or.inr ha, Or.inr ha⟩
    have hpre := hGS.union' hmeet hUS
    have hGsub : G ⊆ (frontier U \ S)ᶜ := by
      intro p hp hpbad
      have hpG := hfront hpbad.1
      rw [hGo.frontier_eq] at hpG
      exact hpG.2 hp
    have hUsub : U ⊆ (frontier U \ S)ᶜ := by
      intro p hp hpbad
      have hpU := hpbad.1
      rw [hUo.frontier_eq] at hpU
      exact hpU.2 hp
    have hSsub : S ⊆ (frontier U \ S)ᶜ := by
      intro p hp hpbad
      exact hpbad.2 hp
    exact hpre.subset_connectedComponentIn (Or.inl (Or.inl hx))
      (union_subset (union_subset hGsub hSsub) (union_subset hUsub hSsub))
      (Or.inr (Or.inl hy))

/-- Almost surely, each compactly contained cluster and each complementary
component are separated by the component's frontier, and are joined after any
nonempty subset of that frontier is removed. Only volume growth is assumed. -/
theorem ae_cluster_frontier_deletion_separation
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ S ⊆ frontier U, ∀ x ∈ cluster (μ ω) 1 z t, ∀ y ∈ U,
        y ∈ connectedComponentIn (frontier U \ S)ᶜ x ↔ S.Nonempty := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU S hS x hx y hy
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hc := hcluster t 1 ht zero_lt_one z hz
  obtain ⟨p, hp, hUeq⟩ := hU
  have hUs : U ⊆ (closure (cluster (μ ω) 1 z t))ᶜ := by
    rw [← hUeq]
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint (cluster (μ ω) 1 z t) U := by
    rw [disjoint_left]
    intro v hv hvU
    exact hUs hvU (subset_closure hv)
  exact mem_connectedComponentIn_compl_frontier_sdiff_iff hc.1 hc.2.1 hg.1 hg.2.1
    hdis hg.2.2.2.1 hS hx hy

end HarmonicBalls

import HarmonicBalls.Proofs.Sec10.ComplementComponents
import HarmonicBalls.Proofs.Sec5.NoEntryTopology

/-!
# Minimal separation by complementary frontiers

Every point on a complementary frontier is approached both from the cluster
and from the complementary component. Hence a proper closed subset of that
frontier cannot separate these two connected open sets.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The frontier of an open set separates any point of the set from any
point outside its closure. -/
theorem not_mem_connectedComponentIn_compl_frontier
    {U : Set ℂ} (hU : IsOpen U) {x y : ℂ} (hxU : x ∉ U)
    (hxf : x ∉ frontier U) (hyU : y ∈ U) :
    y ∉ connectedComponentIn (frontier U)ᶜ x := by
  intro hy
  have hdis : Disjoint (connectedComponentIn (frontier U)ᶜ x) (frontier U) := by
    rw [disjoint_left]
    intro p hp hpf
    exact connectedComponentIn_subset _ _ hp hpf
  rcases IsPreconnected.subset_or_disjoint_of_disjoint_frontier isPreconnected_connectedComponentIn hU hdis with hsub | hdisU
  · exact hxU (hsub (mem_connectedComponentIn hxf))
  · exact (disjoint_left.mp hdisU) hy hyU

/-- If two connected open sets share every point of the frontier of the
second, then every proper closed part of that frontier leaves the two sets
in the same component of its complement. -/
theorem mem_connectedComponentIn_compl_of_proper_frontier_subset
    {G U A : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hfront : frontier U ⊆ frontier G) (hAc : IsClosed A)
    (hA : A ⊆ frontier U) {q : ℂ} (hq : q ∈ frontier U) (hqA : q ∉ A)
    {x y : ℂ} (hx : x ∈ G) (hy : y ∈ U) :
    y ∈ connectedComponentIn Aᶜ x := by
  have hGsub : G ⊆ Aᶜ := by
    intro p hp hpA
    have hpfront := hfront (hA hpA)
    rw [hGo.frontier_eq] at hpfront
    exact hpfront.2 hp
  have hUsub : U ⊆ Aᶜ := by
    intro p hp hpA
    have hpfront := hA hpA
    rw [hUo.frontier_eq] at hpfront
    exact hpfront.2 hp
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hAc.isOpen_compl q hqA
  have hqG : q ∈ closure G := frontier_subset_closure (hfront hq)
  have hqU : q ∈ closure U := frontier_subset_closure hq
  obtain ⟨g, hgball, hgG⟩ := mem_closure_iff.mp hqG _ isOpen_ball (mem_ball_self hr)
  obtain ⟨v, hvball, hvU⟩ := mem_closure_iff.mp hqU _ isOpen_ball (mem_ball_self hr)
  have hGcomp : G ⊆ connectedComponentIn Aᶜ x :=
    hGc.isPreconnected.subset_connectedComponentIn hx hGsub
  have hgcomp : g ∈ connectedComponentIn Aᶜ x := hGcomp hgG
  have hballcomp : ball q r ⊆ connectedComponentIn Aᶜ x := by
    have h := (isConnected_ball hr).isPreconnected.subset_connectedComponentIn hgball hrsub
    rw [← connectedComponentIn_eq hgcomp] at h
    exact h
  have hvcomp : v ∈ connectedComponentIn Aᶜ x := hballcomp hvball
  have hUcomp : U ⊆ connectedComponentIn Aᶜ x := by
    have h := hUc.isPreconnected.subset_connectedComponentIn hvU hUsub
    rw [← connectedComponentIn_eq hvcomp] at h
    exact h
  exact hUcomp hy

/-- The common frontier is a minimal closed separator of points in the two
connected open sets: it separates them, and no proper closed subset does. -/
theorem frontier_minimal_closed_separator
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {x y : ℂ} (hx : x ∈ G) (hy : y ∈ U) :
    y ∉ connectedComponentIn (frontier U)ᶜ x ∧
      ∀ A : Set ℂ, IsClosed A → A ⊆ frontier U →
        (∃ q ∈ frontier U, q ∉ A) → y ∈ connectedComponentIn Aᶜ x := by
  have hxU : x ∉ U := fun hxU => disjoint_left.mp hdis hx hxU
  have hxf : x ∉ frontier U := by
    intro h
    have hG := hfront h
    rw [hGo.frontier_eq] at hG
    exact hG.2 hx
  refine ⟨not_mem_connectedComponentIn_compl_frontier hUo hxU hxf hy, ?_⟩
  intro A hAc hA ⟨q, hq, hqA⟩
  exact mem_connectedComponentIn_compl_of_proper_frontier_subset hGo hGc hUo hUc
    hfront hAc hA hq hqA hx hy

/-- For every compactly contained cluster, a complementary frontier is a
minimal closed separator between the cluster and that component. Only volume
growth is assumed. -/
theorem ae_cluster_frontier_minimal_separation
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ A : Set ℂ, IsClosed A → A ⊆ frontier U →
      ∀ q ∈ frontier U, q ∉ A → ∀ x ∈ cluster (μ ω) 1 z t, ∀ y ∈ U,
        y ∉ connectedComponentIn (frontier U)ᶜ x ∧ y ∈ connectedComponentIn Aᶜ x := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU A hAc hA q hq hqA x hx y hy
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
  have h := frontier_minimal_closed_separator hc.1 hc.2.1 hg.1 hg.2.1 hdis
    hg.2.2.2.1 hx hy
  exact ⟨h.1, h.2 A hAc hA ⟨q, hq, hqA⟩⟩

end HarmonicBalls

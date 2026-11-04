import HarmonicBalls.Proofs.Sec10.FrontierMinimalSeparation

/-!
# Paths crossing a frontier near a prescribed point

Minimal separation permits a path from the cluster to a complementary
component that meets their common frontier only inside an arbitrarily small
ball about any chosen frontier point.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- For every common-frontier point and neighborhood ball there is a path
from the first connected open set to the second that avoids the frontier
outside the ball. -/
theorem joinedIn_frontier_compl_outside_ball
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {x y q : ℂ}
    (hx : x ∈ G) (hy : y ∈ U) (hq : q ∈ frontier U)
    {r : ℝ} (hr : 0 < r) :
    JoinedIn (frontier U \ ball q r)ᶜ x y := by
  let A := frontier U \ ball q r
  have hAc : IsClosed A := isClosed_frontier.sdiff isOpen_ball
  have hAs : A ⊆ frontier U := sdiff_subset
  have hqA : q ∉ A := fun h => h.2 (mem_ball_self hr)
  have hsep := frontier_minimal_closed_separator hGo hGc hUo hUc hdis hfront hx hy
  have hycomp : y ∈ connectedComponentIn Aᶜ x := hsep.2 A hAc hAs ⟨q, hq, hqA⟩
  have hxA : x ∈ Aᶜ := by
    intro hxA
    have hxf := hfront (hAs hxA)
    rw [hGo.frontier_eq] at hxf
    exact hxf.2 hx
  have hcomp : IsConnected (connectedComponentIn Aᶜ x) :=
    isConnected_connectedComponentIn_iff.mpr hxA
  have hpath := (hAc.isOpen_compl.connectedComponentIn.isConnected_iff_isPathConnected.mp hcomp).joinedIn
    x (mem_connectedComponentIn hxA) y hycomp
  exact hpath.mono (connectedComponentIn_subset _ _)

/-- The localized path necessarily meets the frontier, and every such
meeting lies in the prescribed ball. -/
theorem exists_path_crossing_frontier_in_ball
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {x y q : ℂ}
    (hx : x ∈ G) (hy : y ∈ U) (hq : q ∈ frontier U)
    {r : ℝ} (hr : 0 < r) :
    ∃ p : Path x y, (∀ s, p s ∈ frontier U → p s ∈ ball q r) ∧
      ∃ s, p s ∈ frontier U := by
  obtain ⟨p, hp⟩ := joinedIn_frontier_compl_outside_ball hGo hGc hUo hUc
    hdis hfront hx hy hq hr
  refine ⟨p, ?_, ?_⟩
  · intro s hs
    by_contra hnot
    exact hp s ⟨hs, hnot⟩
  · by_contra hn
    have havoid : range p ⊆ (frontier U)ᶜ := by
      rintro w ⟨s, rfl⟩ hw
      exact hn ⟨s, hw⟩
    have hxrange : x ∈ range p := ⟨0, p.source⟩
    have hyrange : y ∈ range p := ⟨1, p.target⟩
    have hycomp := (isConnected_range p.continuous).isPreconnected.subset_connectedComponentIn
      hxrange havoid hyrange
    exact (frontier_minimal_closed_separator hGo hGc hUo hUc hdis hfront hx hy).1 hycomp

/-- Almost surely, every point of a complementary cluster frontier admits
paths between the cluster and the component which meet that frontier only
inside any prescribed neighborhood of the point. -/
theorem ae_cluster_localized_frontier_paths
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ x ∈ cluster (μ ω) 1 z t, ∀ y ∈ U, ∀ q ∈ frontier U, ∀ r : ℝ, 0 < r →
        ∃ p : Path x y, (∀ s, p s ∈ frontier U → p s ∈ ball q r) ∧
          ∃ s, p s ∈ frontier U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU x hx y hy q hq r hr
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hc := hcluster t 1 ht zero_lt_one z hz
  obtain ⟨v, hv, hUeq⟩ := hU
  have hUs : U ⊆ (closure (cluster (μ ω) 1 z t))ᶜ := by
    rw [← hUeq]
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint (cluster (μ ω) 1 z t) U := by
    rw [disjoint_left]
    intro w hw hwU
    exact hUs hwU (subset_closure hw)
  exact exists_path_crossing_frontier_in_ball hc.1 hc.2.1 hg.1 hg.2.1 hdis
    hg.2.2.2.1 hx hy hq hr

end HarmonicBalls

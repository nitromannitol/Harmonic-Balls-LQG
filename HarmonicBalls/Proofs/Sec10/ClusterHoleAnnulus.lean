import HarmonicBalls.Proofs.Sec10.WholeAnnulusHoleCrossing
import HarmonicBalls.Proofs.Sec10.ComplementaryHolePacking
import HarmonicBalls.Proofs.Sec10.FrontierPerfect

/-! # Annular witnesses from distinct complementary components

Two distinct complementary components produce an explicit whole-annulus
obstruction to the crossing-containment conclusion. The hypothesis that two
such components exist is retained; no existence of LQG holes is asserted.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- Almost surely, any two distinct components of the complement of a
compactly contained cluster give an annulus in the second component. The
whole annulus is the crossing component for the complement of the first,
while the cluster has no crossing and the first frontier is missed. -/
theorem ae_distinct_cluster_complement_components_have_annular_obstruction
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ, U ≠ V →
      ∃ (w : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧
        closure (annulus w r R) ⊆ V ∩ ball 0 1 ∧
        crossingComponents (Uᶜ ∩ annulus w r R) w r R = {annulus w r R} ∧
        crossingComponents (cluster (μ ω) 1 z t ∩ annulus w r R) w r R = ∅ ∧
        Disjoint (closure (annulus w r R)) (frontier U) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    ae_cluster_frontier_perfect hI2 γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ]
    with ω hgeom hperfect
  intro t ht z hz hcl U hU V hV hne
  have hg := hgeom t 1 ht zero_lt_one z hz hcl V hV
  obtain ⟨p, hp⟩ := (hperfect t ht z hz hcl V hV).1
  have hpball : p ∈ ball (0 : ℂ) 1 := hg.2.2.2.2 (subset_closure hp)
  obtain ⟨q, hqball, hqV⟩ := mem_closure_iff.mp (frontier_subset_closure hp)
    (ball 0 1) isOpen_ball hpball
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hg.1.inter isOpen_ball) q ⟨hqV, hqball⟩
  have hball : closedBall q (ε / 2) ⊆ V ∩ ball (0 : ℂ) 1 :=
    (closedBall_subset_ball (by linarith)).trans hεsub
  have hr : 0 < ε / 4 := by positivity
  have hrR : ε / 4 < ε / 2 := by linarith
  have hann : annulus q (ε / 4) (ε / 2) ⊆ closedBall q (ε / 2) := by
    intro x hx
    exact ball_subset_closedBall hx.1
  have hsub : closure (annulus q (ε / 4) (ε / 2)) ⊆ V ∩ ball 0 1 :=
    (closure_minimal hann isClosed_closedBall).trans hball
  have hGV : Disjoint (cluster (μ ω) 1 z t) V := by
    apply disjoint_left.mpr
    intro x hx hxV
    obtain ⟨v, hv, hVeq⟩ := hV
    have hxnot : x ∈ (closure (cluster (μ ω) 1 z t))ᶜ := by
      rw [← hVeq] at hxV
      exact connectedComponentIn_subset _ _ hxV
    exact hxnot (subset_closure hx)
  have hUV : Disjoint U V :=
    connectedComponentsIn_pairwise_disjoint _ hU hV hne
  have hw := complementary_hole_crossing_is_whole_annulus hGV hUV hg.1 q hr hrR
    (hball.trans inter_subset_left)
  exact ⟨q, ε / 4, ε / 2, hr, hrR, hsub, hw.1, hw.2.1, hw.2.2.2⟩

end HarmonicBalls

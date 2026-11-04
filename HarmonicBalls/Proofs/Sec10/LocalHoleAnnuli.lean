import HarmonicBalls.Proofs.Sec10.ClusterHoleAnnulus

/-! # Arbitrarily small annular obstructions in complementary components

Every point of a second complementary component inside the unit disk is the
centre of arbitrarily small whole-annulus obstructions. The existence of a
second component is a hypothesis, not an assertion about LQG clusters.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- At every point of an open region disjoint from `G` and `U`, there are
arbitrarily small annuli witnessing failure of crossing containment. -/
theorem complementary_hole_has_arbitrarily_small_annuli
    {G U V : Set ℂ} (hGV : Disjoint G V) (hUV : Disjoint U V)
    (hV : IsOpen V) {w : ℂ} (hw : w ∈ V ∩ ball (0 : ℂ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ R < ε ∧
      closure (annulus w r R) ⊆ V ∩ ball 0 1 ∧
      crossingComponents (Uᶜ ∩ annulus w r R) w r R = {annulus w r R} ∧
      crossingComponents (G ∩ annulus w r R) w r R = ∅ ∧
      Disjoint (closure (annulus w r R)) (frontier U) := by
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hV.inter isOpen_ball) w hw
  let R := min δ ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRδ : R < δ := by dsimp [R]; have := min_le_left δ ε; linarith
  have hRε : R < ε := by dsimp [R]; have := min_le_right δ ε; linarith
  have hball : closedBall w R ⊆ V ∩ ball (0 : ℂ) 1 :=
    (closedBall_subset_ball hRδ).trans hδsub
  have hr : 0 < R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  have hcl : closure (annulus w (R / 2) R) ⊆ V ∩ ball 0 1 := by
    apply (closure_minimal ?_ isClosed_closedBall).trans hball
    intro x hx
    exact ball_subset_closedBall hx.1
  have hcross := complementary_hole_crossing_is_whole_annulus hGV hUV hV w hr hrR
    (hball.trans inter_subset_left)
  exact ⟨R / 2, R, hr, hrR, hRε, hcl, hcross.1, hcross.2.1, hcross.2.2.2⟩

/-- Under volume growth, any two distinct components of a compactly contained
cluster complement have the local annular obstruction at every point of the
second component inside the unit disk. -/
theorem ae_cluster_complement_local_annular_obstruction
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ, U ≠ V →
      ∀ w ∈ V ∩ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      ∃ r R : ℝ, 0 < r ∧ r < R ∧ R < ε ∧
        closure (annulus w r R) ⊆ V ∩ ball 0 1 ∧
        crossingComponents (Uᶜ ∩ annulus w r R) w r R = {annulus w r R} ∧
        crossingComponents (cluster (μ ω) 1 z t ∩ annulus w r R) w r R = ∅ ∧
        Disjoint (closure (annulus w r R)) (frontier U) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hgeom
  intro t ht z hz hcl U hU V hV hne w hw ε hε
  have hVopen := (hgeom t 1 ht zero_lt_one z hz hcl V hV).1
  have hGV : Disjoint (cluster (μ ω) 1 z t) V := by
    apply disjoint_left.mpr
    intro x hx hxV
    obtain ⟨v, hv, hVeq⟩ := hV
    have hxnot : x ∈ (closure (cluster (μ ω) 1 z t))ᶜ := by
      rw [← hVeq] at hxV
      exact connectedComponentIn_subset _ _ hxV
    exact hxnot (subset_closure hx)
  exact complementary_hole_has_arbitrarily_small_annuli hGV
    (connectedComponentsIn_pairwise_disjoint _ hU hV hne) hVopen hw hε

end HarmonicBalls

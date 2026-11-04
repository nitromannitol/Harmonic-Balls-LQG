import HarmonicBalls.Proofs.Sec10.PointwiseHoleCriterion
import HarmonicBalls.Proofs.Sec10.SparseCrossingsNoHoles

/-! # Countable annular tests for absence of holes

For a fixed pole, countably many annular crossing-containment assertions imply
connectedness of every closed-cluster complement. These assertions are
hypotheses; this result does not establish them for LQG clusters.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

/-- At a point of a bounded complementary component, fixed-ratio annuli at
arbitrarily small prescribed reciprocal-integer radii obstruct crossing
containment for the exterior component. -/
theorem not_bounded_point_component_of_reciprocal_crossings
    {G : Set ℂ} (hG : closure G ⊆ closedBall 0 1) {w : ℂ}
    (hw : w ∈ (closure G)ᶜ)
    (hcross : ∀ n : ℕ,
      let r : ℝ := 1 / ((n : ℝ) + 1)
      closure (annulus w r (2 * r)) ⊆ ball 0 1 →
      ∀ C ∈ crossingComponents
          ((connectedComponentIn (closure G)ᶜ (2 : ℂ))ᶜ ∩ annulus w r (2 * r)) w r (2 * r),
        ∃ C' ∈ crossingComponents (G ∩ annulus w r (2 * r)) w r (2 * r), C' ⊆ C) :
    ¬ Bornology.IsBounded (connectedComponentIn (closure G)ᶜ w) := by
  let V := connectedComponentIn (closure G)ᶜ w
  let U := connectedComponentIn (closure G)ᶜ (2 : ℂ)
  have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  have hpG : (2 : ℂ) ∈ (closure G)ᶜ := (compl_subset_compl.mpr hG) hp
  have hU : U ∈ connectedComponentsIn (closure G)ᶜ := ⟨2, hpG, rfl⟩
  have hV : V ∈ connectedComponentsIn (closure G)ᶜ := ⟨w, hw, rfl⟩
  have hwV : w ∈ V := mem_connectedComponentIn hw
  have hVo : IsOpen V := isClosed_closure.isOpen_compl.connectedComponentIn
  intro hb
  have hVball : V ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure hG hV hb
  have hUV : Disjoint U V := by
    apply connectedComponentsIn_pairwise_disjoint _ hU hV
    intro heq
    have hbU : Bornology.IsBounded U := by rw [heq]; exact hb
    exact not_isBounded_exterior_component zero_lt_one hG hp hbU
  have hGV : Disjoint G V := by
    apply disjoint_left.mpr
    intro x hx hxV
    exact (connectedComponentIn_subset _ _ hxV) (subset_closure hx)
  obtain ⟨δ, hδ, hδcross⟩ := complementary_hole_fixed_ratio_all_small hGV hUV hVo
    ⟨hwV, hVball hwV⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let r : ℝ := 1 / ((n : ℝ) + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by simpa [r] using hn
  obtain ⟨hcl, hUcross, hGcross, _⟩ := hδcross r hr hrδ
  have hmem : annulus w r (2 * r) ∈ crossingComponents (Uᶜ ∩ annulus w r (2 * r)) w r (2 * r) := by
    rw [hUcross]
    exact mem_singleton _
  obtain ⟨C, hC, _⟩ := hcross n (hcl.trans inter_subset_right) _ hmem
  rw [hGcross] at hC
  simp at hC

universe u

/-- For one fixed pole, crossing containment at rational times, a countable
    dense set of centres, and reciprocal-integer radii suffices to rule out
    holes at every positive time. The countable tests are explicit premises. -/
theorem ae_cluster_compl_connected_of_countable_crossing_tests
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1)
    (D : Set ℂ) (hDcount : D.Countable) (hDdense : Dense D)
    (htest : ∀ (q : ℚ) (w : D) (n : ℕ), 0 < (q : ℝ) → ∀ᵐ ω ∂P,
      let r : ℝ := 1 / ((n : ℝ) + 1)
      let G := cluster (μ ω) 1 z q
      closure (annulus (w : ℂ) r (2 * r)) ⊆ ball 0 1 →
      ∀ C ∈ crossingComponents
          ((connectedComponentIn (closure G)ᶜ (2 : ℂ))ᶜ ∩ annulus (w : ℂ) r (2 * r))
          (w : ℂ) r (2 * r),
        ∃ C' ∈ crossingComponents (G ∩ annulus (w : ℂ) r (2 * r)) (w : ℂ) r (2 * r), C' ⊆ C) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → IsConnected (closure (cluster (μ ω) 1 z t))ᶜ := by
  apply ae_cluster_compl_connected_of_pointwise_rational_exclusion hI2 h611 h82
    hγ hγ2 hα P hC hcirc μ hGFF hμ z hz D hDcount hDdense
  intro q w hq
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      let r : ℝ := 1 / ((n : ℝ) + 1)
      let G := cluster (μ ω) 1 z q
      closure (annulus (w : ℂ) r (2 * r)) ⊆ ball 0 1 →
      ∀ C ∈ crossingComponents
          ((connectedComponentIn (closure G)ᶜ (2 : ℂ))ᶜ ∩ annulus (w : ℂ) r (2 * r))
          (w : ℂ) r (2 * r),
        ∃ C' ∈ crossingComponents (G ∩ annulus (w : ℂ) r (2 * r)) (w : ℂ) r (2 * r), C' ⊆ C :=
    ae_all_iff.mpr fun n => htest q w n hq
  filter_upwards [hall] with ω hω hw
  apply not_bounded_point_component_of_reciprocal_crossings _ hw hω
  exact closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall

end HarmonicBalls

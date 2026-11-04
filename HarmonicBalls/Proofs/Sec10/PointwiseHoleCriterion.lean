import HarmonicBalls.Proofs.Sec10.HolePersistenceAtBoundaryContact
import HarmonicBalls.Proofs.Sec10.ExteriorComponent

/-! # Pointwise detection of holes

A countable dense set detects every open complementary component. Combined
with persistence in time, pointwise exclusion at positive rational times
suffices to exclude holes at all positive times for a fixed pole.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- A dense set meets every bounded component of the complement of a closed
set, and its point component is that bounded component. -/
theorem no_bounded_complement_component_of_dense_points {K D : Set ℂ}
    (hK : IsClosed K) (hD : Dense D)
    (hpoint : ∀ x ∈ D, x ∈ Kᶜ →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
    ∀ U ∈ connectedComponentsIn Kᶜ, ¬ Bornology.IsBounded U := by
  intro U hU hb
  obtain ⟨p, hp, hpU⟩ := hU
  have hopen : IsOpen U := by
    rw [← hpU]
    exact hK.isOpen_compl.connectedComponentIn
  have hne : U.Nonempty := ⟨p, hpU ▸ mem_connectedComponentIn hp⟩
  obtain ⟨x, hxU, hxD⟩ := hD.inter_open_nonempty U hopen hne
  have heq : connectedComponentIn Kᶜ x = U := by
    rw [← hpU] at hxU ⊢
    exact (connectedComponentIn_eq hxU).symm
  have hx : x ∈ Kᶜ := by
    rw [← hpU] at hxU
    exact connectedComponentIn_subset _ _ hxU
  exact hpoint x hxD hx (heq ▸ hb)

universe u

/-- For one fixed pole, pointwise exclusion at each positive rational time
and each point of a countable dense set yields connected complements at all
positive times. The pointwise exclusion is an explicit hypothesis. -/
theorem ae_cluster_compl_connected_of_pointwise_rational_exclusion
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
    (hpoint : ∀ (q : ℚ) (x : D), 0 < (q : ℝ) → ∀ᵐ ω ∂P,
      (x : ℂ) ∈ (closure (cluster (μ ω) 1 z q))ᶜ →
        ¬ Bornology.IsBounded (connectedComponentIn
          (closure (cluster (μ ω) 1 z q))ᶜ x)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      IsConnected (closure (cluster (μ ω) 1 z t))ᶜ := by
  let : Countable D := hDcount.to_subtype
  have hcount : ∀ᵐ ω ∂P, ∀ (q : ℚ) (x : D), 0 < (q : ℝ) →
      (x : ℂ) ∈ (closure (cluster (μ ω) 1 z q))ᶜ →
        ¬ Bornology.IsBounded (connectedComponentIn
          (closure (cluster (μ ω) 1 z q))ᶜ x) := by
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro x
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [hpoint q x hq] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hcount, ae_cluster_no_holes_iff_no_rational_holes hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpoints htime
  have hrat : ∀ q : ℚ, 0 < (q : ℝ) → ∀ U ∈ connectedComponentsIn
      (closure (cluster (μ ω) 1 z q))ᶜ, ¬ Bornology.IsBounded U := by
    intro q hq
    apply no_bounded_complement_component_of_dense_points isClosed_closure hDdense
    intro x hx
    exact hpoints q ⟨x, hx⟩ hq
  have hnone := (htime z hz).2 hrat
  intro t ht
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  apply Classical.byContradiction
  intro hnot
  obtain ⟨U, hU, hb⟩ :=
    (not_isConnected_compl_iff_exists_bounded_component zero_lt_one hcl hp).1 hnot
  exact hnone t ht U hU hb

end HarmonicBalls

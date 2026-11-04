import HarmonicBalls.Proofs.Sec5.InteriorHausdorffContinuity
import HarmonicBalls.Proofs.Sec10.HolePersistenceAtBoundaryContact

/-! # Compact subsets of holes persist

Interior right continuity of the closed clusters keeps a compact connected
subset of a complementary component inside one of its descendants for a
positive interval, including after unit-boundary contact.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- No new interior points in the right limit imply that a closed connected
subset of an interior complementary component stays together in a descendant
component for a positive interval. -/
theorem complement_component_compact_subset_persists
    {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hinter : (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t))
    {U K : Set ℂ} (hU : U ∈ connectedComponentsIn (closure (F t))ᶜ)
    (hKclosed : IsClosed K) (hKconnected : IsConnected K)
    (hKU : K ⊆ U) (hKdisc : K ⊆ ball (0 : ℂ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      ∃ V ∈ connectedComponentsIn (closure (F s))ᶜ, K ⊆ V ∧ V ⊆ U := by
  obtain ⟨p, hp⟩ := hKconnected.nonempty
  have hUsub : U ⊆ (closure (F t))ᶜ := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact connectedComponentIn_subset _ _
  have hlim : (⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))) ⊆ Kᶜ := by
    intro x hx hxK
    have hxcl := hinter ⟨by simpa only [dyadicScale] using hx, hKdisc hxK⟩
    exact hUsub (hKU hxK) hxcl
  obtain ⟨δ, hδ, hδsub⟩ := eventually_closure_subset_open_of_iInter_subset
    ht hmono hbound hKclosed.isOpen_compl hlim
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  have hKout : K ⊆ (closure (F s))ᶜ := by
    intro x hxK hxcl
    exact hδsub s hs hxcl hxK
  let V := connectedComponentIn (closure (F s))ᶜ p
  have hpout := hKout hp
  have hV : V ∈ connectedComponentsIn (closure (F s))ᶜ := ⟨p, hpout, rfl⟩
  have hKV : K ⊆ V := hKconnected.isPreconnected.subset_connectedComponentIn hp hKout
  have hVU : V ⊆ U := by
    obtain ⟨x, hx, hUx⟩ := hU
    have hpU : p ∈ connectedComponentIn (closure (F t))ᶜ x := hUx.symm ▸ hKU hp
    have heq : connectedComponentIn (closure (F t))ᶜ p = U :=
      (connectedComponentIn_eq hpU).symm.trans hUx
    exact heq ▸ connectedComponentIn_mono p (compl_subset_compl.mpr (closure_mono (hmono t s ht hs.1)))
  exact ⟨V, hV, hKV, hVU⟩

universe u

/-- The interior time-continuity estimates imply that every compact connected
subset of a bounded hole remains in a single bounded descendant for a right
interval. All estimates used for interior continuity remain explicit. -/
theorem ae_cluster_hole_compact_connected_subset_persists
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ K : Set ℂ, IsCompact K → IsConnected K → K ⊆ U →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ K ⊆ V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume
      (clusterOpenLaplacian_proved hI2) (clusterMonotone_proved hI2)
      (clusterConservationOfMass_proved hI2) h61 h611 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hmono hinter
  intro t ht z hz U hU hb K hK hc hKU
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure hcl hU hb
  obtain ⟨δ, hδ, hpersist⟩ := complement_component_compact_subset_persists ht
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball) (hinter t ht z hz) hU hK.isClosed hc hKU
    (hKU.trans hUdisc)
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  obtain ⟨V, hV, hKV, hVU⟩ := hpersist s hs
  exact ⟨V, hV, hb.subset hVU, hKV, hVU⟩

/-- Every point of a bounded hole has a closed ball that stays inside a
single descendant throughout a right interval, even at boundary contact. -/
theorem ae_cluster_hole_closedBall_persists
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ p ∈ U,
      ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ closedBall p r ⊆ V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_compact_connected_subset_persists hI2 hvolume h61 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro t ht z hz U hU hb p hp
  have hUopen : IsOpen U := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen p hp
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : closedBall p (ε / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨δ, hδ, hdesc⟩ := hpersist t ht z hz U hU hb (closedBall p (ε / 2))
    (isCompact_closedBall _ _) (isConnected_closedBall hr.le) hsub
  exact ⟨ε / 2, δ, hr, hδ, hdesc⟩

end HarmonicBalls

import HarmonicBalls.Proofs.Sec10.HoleCompactPersistence
import HarmonicBalls.Proofs.Sec10.ComplementaryHolePacking

/-! # Persistence of hole inradii

Compact balls inside finitely many holes persist together in distinct later
holes. This gives a rational-time reduction for bounds on holes of a fixed
positive spatial scale.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- A finite family of holes containing closed balls of radius `r` injects
into later holes containing closed balls of that radius, on one right interval. -/
theorem ae_finite_large_holes_persist_at_boundary_contact
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ r : ℝ, 0 < r → ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U ∧ ∃ p : ℂ, closedBall p r ⊆ U) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∃ V : {U // U ∈ F} → Set ℂ, Function.Injective V ∧
          ∀ U, V U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ ∧
            Bornology.IsBounded (V U) ∧ V U ⊆ U.1 ∧
              ∃ p : ℂ, closedBall p r ⊆ V U := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_compact_connected_subset_persists hI2 hvolume h61 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro t ht z hz r hr F hF
  have hfinite : ∀ F : Finset (Set ℂ),
      (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
        Bornology.IsBounded U ∧ ∃ p : ℂ, closedBall p r ⊆ U) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∀ U ∈ F, ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U ∧ ∃ p : ℂ, closedBall p r ⊆ V := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨1, zero_lt_one, ?_⟩
        simp
    | @insert U F hUF ih =>
        intro hF
        obtain ⟨hU, hb, p, hp⟩ := hF U (Finset.mem_insert_self U F)
        obtain ⟨δU, hδU, hU⟩ := hpersist t ht z hz U hU hb (closedBall p r)
          (isCompact_closedBall _ _) (isConnected_closedBall hr.le) hp
        obtain ⟨δF, hδF, hF⟩ := ih (by
          intro V hV
          exact hF V (Finset.mem_insert_of_mem hV))
        refine ⟨min δU δF, lt_min hδU hδF, ?_⟩
        intro s hs V hV
        rcases Finset.mem_insert.mp hV with rfl | hV
        · obtain ⟨W, hW, hWb, hpW, hWU⟩ := hU s
            ⟨hs.1, hs.2.trans (add_le_add le_rfl (min_le_left _ _))⟩
          exact ⟨W, hW, hWb, hWU, p, hpW⟩
        · exact hF s ⟨hs.1, hs.2.trans (add_le_add le_rfl (min_le_right _ _))⟩ V hV
  obtain ⟨δ, hδ, hδF⟩ := hfinite F hF
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  choose V hV using fun U : {U // U ∈ F} => hδF s hs U.1 U.2
  refine ⟨V, ?_, hV⟩
  intro U W heq
  apply Subtype.ext
  by_contra hne
  obtain ⟨x, hx, hxV⟩ := (hV U).1
  have hxU : x ∈ U.1 := (hV U).2.2.1 (hxV ▸ mem_connectedComponentIn hx)
  have hxW : x ∈ W.1 := (hV W).2.2.1 (heq ▸ hxV ▸ mem_connectedComponentIn hx)
  exact (disjoint_left.mp (connectedComponentsIn_pairwise_disjoint _
    (hF U.1 U.2).1 (hF W.1 W.2).1 hne)) hxU hxW

/-- A rational-time bound for holes containing a ball of radius `r` also
holds at all positive real times for holes containing a closed ball of radius
`r`. -/
theorem ae_cluster_large_hole_count_bound_of_rational
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ n : ℕ, ∀ r : ℝ, 0 < r →
      (∀ q : ℚ, 0 < (q : ℝ) → ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z q))ᶜ ∧
          Bornology.IsBounded U ∧ ∃ p : ℂ, ball p r ⊆ U) → F.card ≤ n) →
      ∀ t : ℝ, 0 < t → ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U ∧ ∃ p : ℂ, closedBall p r ⊆ U) → F.card ≤ n := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_finite_large_holes_persist_at_boundary_contact hI2 hvolume h61 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz n r hr h t ht F hF
  obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz r hr F hF
  obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
  obtain ⟨V, hVinj, hV⟩ := hp q ⟨htq.le, hq.le⟩
  have hbound := h q (ht.trans htq) (F.attach.image V) (by
    intro U hU
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨hcomp, hb, _, p, hp⟩ := hV W
    exact ⟨hcomp, hb, p, ball_subset_closedBall.trans hp⟩)
  simpa [Finset.card_image_of_injective _ hVinj] using hbound

end HarmonicBalls

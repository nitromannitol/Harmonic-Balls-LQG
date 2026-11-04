import HarmonicBalls.Proofs.Sec10.HoleInteriorMassPersistence
import HarmonicBalls.Proofs.Sec10.HolePersistence

/-! # Hole persistence at boundary contact

Local mass persistence and nullity of the cluster frontier inside the disc
keep a bounded complementary component alive for a right interval, even when
the initial closed cluster meets the boundary of the disc.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- I2 and the explicit Section 6 and 8 estimates imply that every bounded
complementary component persists for a right interval, including when the
initial cluster touches the unit circle. -/
theorem ae_cluster_hole_persists_at_boundary_contact
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
        Bornology.IsBounded V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_bounded_hole_descendant_or_frontier_mass_for_interval hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2) h611 h82 γ α₀ hγ hγ2 hα
      Ω P hC hcirc μ hGFF hμ] with ω hlocal hnull
  intro t ht z hz U hU hb
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure hcl hU hb
  obtain ⟨δ, hδ, hdesc⟩ := hlocal t ht z hz U hU hb
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  rcases hdesc s hs with h | hpositive
  · exact h
  · have hzero : μ ω (frontier (cluster (μ ω) 1 z s) ∩ U) = 0 :=
      measure_mono_null (inter_subset_inter_right _ hUdisc)
        (hnull s (ht.trans_le hs.1) z hz)
    exact ((ne_of_gt hpositive) hzero).elim

/-- Under the same hypotheses, absence of bounded holes at every positive
rational time is equivalent to absence at every positive time. -/
theorem ae_cluster_no_holes_iff_no_rational_holes
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ t : ℝ, 0 < t → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, ¬ Bornology.IsBounded U) ↔
      (∀ q : ℚ, 0 < (q : ℝ) → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z q))ᶜ, ¬ Bornology.IsBounded U) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_persists_at_boundary_contact hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz
  constructor
  · intro h q hq U hU
    exact h q hq U hU
  · intro h t ht U hU hb
    obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz U hU hb
    obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
    obtain ⟨V, hV, hVb, _⟩ := hp q ⟨htq.le, hq.le⟩
    exact h q (ht.trans htq) V hV hVb

/-- Under the same hypotheses, temporal almost-everywhere absence of holes
is equivalent to absence at every positive time, for each pole. -/
theorem ae_cluster_no_holes_iff_hole_times_null
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ t : ℝ, 0 < t → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, ¬ Bornology.IsBounded U) ↔
      volume {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U} = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_persists_at_boundary_contact hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz
  constructor
  · intro hnone
    have heq : {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro t ⟨ht, U, hU, hb⟩
      exact hnone t ht U hU hb
    rw [heq, measure_empty]
  · intro hzero t ht U hU hb
    obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz U hU hb
    have hsub : Ioo t (t + δ) ⊆ {s : ℝ | 0 < s ∧ ∃ V ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z s))ᶜ, Bornology.IsBounded V} := by
      intro s hs
      obtain ⟨V, hV, hVb, _⟩ := hp s ⟨hs.1.le, hs.2.le⟩
      exact ⟨ht.trans hs.1, V, hV, hVb⟩
    have hpos : 0 < volume (Ioo t (t + δ)) :=
      isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr (lt_add_of_pos_right t hδ))
    exact (ne_of_gt hpos) (measure_mono_null hsub hzero)

end HarmonicBalls

import HarmonicBalls.Proofs.Sec10.RationalTimeHoles
import HarmonicBalls.Proofs.Sec10.ComplementaryHolePacking

/-! # Simultaneous persistence of holes

A finite family of bounded complementary components persists during a
common right neighborhood of the cluster time. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

universe u

/-- A bounded hole persists throughout a positive right neighborhood of
its initial cluster time. No later compact containment is required. -/
theorem ae_cluster_hole_persists_on_right_interval
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, t ≤ s → s < t + δ →
      ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
        Bornology.IsBounded V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, h⟩ := ae_cluster_bounded_hole_persists_of_volumeGrowth hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ
  filter_upwards [h] with ω hω
  obtain ⟨hβm, r₀, hr₀, hpersist⟩ := hω
  intro t ht z hz hcl U hU hUb
  have hp2 : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  have hK := hcl.trans ball_subset_closedBall
  have hne : U ≠ connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ (2 : ℂ) := by
    intro heq
    exact not_isBounded_exterior_component zero_lt_one hK hp2 (heq ▸ hUb)
  have hUclosed : U ⊆ closedBall (0 : ℂ) 1 :=
    component_compl_subset_closedBall_of_ne_exterior zero_lt_one hK hp2 hU hne
  obtain ⟨p, hp, hUeq⟩ := hU
  have hpU : p ∈ U := hUeq ▸ mem_connectedComponentIn hp
  have hUopen : IsOpen U := by
    rw [← hUeq]
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  have hUinner : U ⊆ ball (0 : ℂ) 1 := by
    have h := hUopen.subset_interior_iff.mpr hUclosed
    rwa [interior_closedBall (0 : ℂ) one_ne_zero] at h
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hUopen.inter isOpen_ball)
    p ⟨hpU, hUinner hpU⟩
  let r := min ε (r₀ / 2)
  have hr : 0 < r := lt_min hε (half_pos hr₀)
  have hrr : r < r₀ := (min_le_right _ _).trans_lt (half_lt_self hr₀)
  have hrε : r ≤ ε := min_le_left _ _
  have hball : ball p r ⊆ U := (ball_subset_ball hrε).trans (hεsub.trans inter_subset_left)
  have hdisc : ball p r ⊆ ball (0 : ℂ) 1 :=
    (ball_subset_ball hrε).trans (hεsub.trans inter_subset_right)
  refine ⟨r ^ βm, Real.rpow_pos_of_pos hr βm, ?_⟩
  intro s hts hs
  have hsrate : s - t < r ^ βm := by linarith
  obtain ⟨V, hV, hVb, hVU, _⟩ := hpersist t s ht hts z hz hcl U ⟨p, hp, hUeq⟩ hUb
    p r hr hrr hball hdisc hsrate
  exact ⟨V, hV, hVb, hVU⟩

/-- Every finite family of bounded holes persists simultaneously on a
common right neighborhood. The later components lie in the corresponding
original components. -/
theorem ae_finite_cluster_holes_persist_on_right_interval
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, t ≤ s → s < t + δ →
        ∀ U ∈ F, ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_persists_on_right_interval hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro t ht z hz hcl F
  induction F using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, zero_lt_one, ?_⟩
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  | @insert U F hUF ih =>
      intro hF
      have hU := hF U (Finset.mem_insert_self U F)
      obtain ⟨δU, hδU, hU⟩ := hpersist t ht z hz hcl U hU.1 hU.2
      obtain ⟨δF, hδF, hF⟩ := ih (by
        intro V hV
        exact hF V (Finset.mem_insert_of_mem hV))
      refine ⟨min δU δF, lt_min hδU hδF, ?_⟩
      intro s hts hs V hV
      rcases Finset.mem_insert.mp hV with rfl | hV
      · exact hU s hts (hs.trans_le (add_le_add le_rfl (min_le_left _ _)))
      · exact hF s hts (hs.trans_le (add_le_add le_rfl (min_le_right _ _))) V hV

/-- Any finite family of bounded holes injects into the bounded holes at
all sufficiently close later times. -/
theorem ae_finite_cluster_holes_inject_into_later_holes
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ F : Finset (Set ℂ),
        (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, t ≤ s → s < t + δ →
        ∃ V : {U // U ∈ F} → Set ℂ, Function.Injective V ∧
          ∀ U, V U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ ∧
            Bornology.IsBounded (V U) ∧ V U ⊆ U.1 := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_finite_cluster_holes_persist_on_right_interval hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro t ht z hz hcl F hF
  obtain ⟨δ, hδ, hδF⟩ := hpersist t ht z hz hcl F hF
  refine ⟨δ, hδ, ?_⟩
  intro s hts hs
  choose V hV using fun U : {U // U ∈ F} => hδF s hts hs U.1 U.2
  refine ⟨V, ?_, hV⟩
  intro U W heq
  apply Subtype.ext
  by_contra hne
  obtain ⟨x, hx, hxV⟩ := (hV U).1
  have hxU : x ∈ U.1 := (hV U).2.2 (hxV ▸ mem_connectedComponentIn hx)
  have hxW : x ∈ W.1 := (hV W).2.2 (heq ▸ hxV ▸ mem_connectedComponentIn hx)
  exact (disjoint_left.mp (connectedComponentsIn_pairwise_disjoint _
    (hF U.1 U.2).1 (hF W.1 W.2).1 hne)) hxU hxW

end HarmonicBalls

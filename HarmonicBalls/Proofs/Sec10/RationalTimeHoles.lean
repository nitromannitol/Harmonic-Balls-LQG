import HarmonicBalls.Proofs.Sec10.HolePersistence
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences

/-! # Rational-time detection of holes

A bounded hole of a compactly contained cluster persists to arbitrarily
nearby rational times. The typical-point good-scale estimate stays explicit.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

universe u

/-- Under volume growth and the good-scale estimate, every bounded hole
persists to a rational time in any given right neighborhood. The later
cluster need not be compactly contained. -/
theorem ae_cluster_hole_persists_to_rational_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ δ : ℝ, 0 < δ →
      ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < t + δ ∧
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z (q : ℝ)))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, h⟩ := ae_cluster_bounded_hole_persists_of_volumeGrowth hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ
  filter_upwards [h] with ω hω
  obtain ⟨hβm, r₀, hr₀, hpersist⟩ := hω
  intro t ht z hz hcl U hU hUb δ hδ
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
  have hrate : 0 < r ^ βm := Real.rpow_pos_of_pos hr βm
  have hmin : 0 < min δ (r ^ βm) := lt_min hδ hrate
  obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hmin)
  have hqδ : (q : ℝ) < t + δ := lt_of_lt_of_le hq (add_le_add le_rfl (min_le_left _ _))
  have hqrate : (q : ℝ) - t < r ^ βm := by
    have := lt_of_lt_of_le hq (add_le_add le_rfl (min_le_right δ (r ^ βm)))
    linarith
  obtain ⟨V, hV, hVb, hVU, _⟩ := hpersist t q ht htq.le z hz hcl U ⟨p, hp, hUeq⟩ hUb
    p r hr hrr hball hdisc hqrate
  exact ⟨q, htq, hqδ, V, hV, hVb, hVU⟩

/-- If the cluster is compactly contained again at some later time, a
bounded hole persists to an intermediate rational time with the same
compact-containment property. -/
theorem ae_cluster_hole_persists_to_compact_rational_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t T : ℝ, 0 < t → t < T → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      closure (cluster (μ ω) 1 z T) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U →
      ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < T ∧
        closure (cluster (μ ω) 1 z (q : ℝ)) ⊆ ball 0 1 ∧
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z (q : ℝ)))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_persists_to_rational_time hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hpersist hmono
  intro t T ht htT z hz hcl hclT U hU hb
  obtain ⟨q, htq, hqT, V, hV, hVb, hVU⟩ :=
    hpersist t ht z hz hcl U hU hb (T - t) (sub_pos.mpr htT)
  have hqT' : (q : ℝ) < T := by linarith
  have hqpos : 0 < (q : ℝ) := ht.trans htq
  have hqcl : closure (cluster (μ ω) 1 z (q : ℝ)) ⊆ ball 0 1 :=
    (closure_mono (hmono q T 1 hqpos hqT'.le zero_lt_one z hz)).trans hclT
  exact ⟨q, htq, hqT', hqcl, V, hV, hVb, hVU⟩

/-- To rule out holes at compactly contained times having a later compact
containment, it suffices to rule them out at compactly contained positive
rational times. -/
theorem ae_no_cluster_holes_of_rational_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ q : ℚ, 0 < (q : ℝ) →
        closure (cluster (μ ω) 1 z (q : ℝ)) ⊆ ball 0 1 →
        ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z (q : ℝ)))ᶜ,
          ¬ Bornology.IsBounded V) →
      ∀ t T : ℝ, 0 < t → t < T →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        closure (cluster (μ ω) 1 z T) ⊆ ball 0 1 →
        ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          ¬ Bornology.IsBounded U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_persists_to_compact_rational_time hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz hrat t T ht htT hcl hclT U hU hUb
  obtain ⟨q, htq, _, hqcl, V, hV, hVb, _⟩ :=
    hpersist t T ht htT z hz hcl hclT U hU hUb
  exact hrat q (ht.trans htq) hqcl V hV hVb

end HarmonicBalls

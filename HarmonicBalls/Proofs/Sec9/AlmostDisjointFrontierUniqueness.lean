import HarmonicBalls.Proofs.Sec9.BoundaryExteriorDefect

/-!
# Weak uniqueness for almost disjoint boundary families

Only countably many members of an almost disjoint family of comparison
frontiers can carry positive mass. This gives weak uniqueness outside a
countable family of indices, without the boundary-null theorem.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u v

/-- In an s-finite measure space, a family of pairwise almost disjoint
frontiers has at most countably many members of positive mass. -/
theorem countable_positive_measure_frontiers
    {ι : Type v} (μ : Measure ℂ) [SFinite μ] (A : ι → Set ℂ)
    (hpair : ∀ i j, i ≠ j → μ (frontier (A i) ∩ frontier (A j)) = 0) :
    {i : ι | 0 < μ (frontier (A i))}.Countable := by
  apply Measure.countable_meas_pos_of_disjoint_iUnion₀
  · intro i
    exact isClosed_frontier.measurableSet.nullMeasurableSet
  · intro i j hij
    exact hpair i j hij

/-- On the I2 event, each family of comparison sets with pairwise almost
 disjoint frontiers has only countably many possible failures of weak
uniqueness. The exceptional indices may depend on the measure and family;
the event itself works simultaneously for every family. -/
theorem ae_subharmonicBall_uniqueness_off_countable_frontier_family
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (ι : Type v) (A : ι → Set ℂ),
      (∀ i j, i ≠ j → μ ω (frontier (A i) ∩ frontier (A j)) = 0) →
      ∃ E : Set ι, E.Countable ∧ ∀ i ∉ E, ∀ (z : ℂ) (t R : ℝ),
        0 < t → 0 < R → z ∈ ball (0 : ℂ) R → closure (A i) ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) (A i) z → μ ω (A i) = ENNReal.ofReal t →
        cluster (μ ω) R z t ⊆ A i ∧ A i ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen (A i) → regularizedCluster (μ ω) R z t = A i) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2 γ α₀ hγ hγ2 hα
      Ω P hC hcirc μ hGFF hμ] with ω hV hunique
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  intro ι A hpair
  refine ⟨{i | 0 < μ ω (frontier (A i))},
    countable_positive_measure_frontiers (μ ω) A hpair, ?_⟩
  intro i hi z t R ht hR hz hcl hA hmass
  have hnull : μ ω (frontier (A i)) = 0 := by
    exact le_antisymm (not_lt.mp hi) bot_le
  apply hunique (A i) z t R ht hR hz hcl hA hmass
  exact measure_mono_null inter_subset_right hnull

/-- I2 makes singleton sets null. Hence a family whose frontiers meet
pairwise in countable sets has at most countably many exceptional members
for weak uniqueness, on a single event for all such families. -/
theorem ae_subharmonicBall_uniqueness_off_countable_intersection_family
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (ι : Type v) (A : ι → Set ℂ),
      (∀ i j, i ≠ j → (frontier (A i) ∩ frontier (A j)).Countable) →
      ∃ E : Set ι, E.Countable ∧ ∀ i ∉ E, ∀ (z : ℂ) (t R : ℝ),
        0 < t → 0 < R → z ∈ ball (0 : ℂ) R → closure (A i) ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) (A i) z → μ ω (A i) = ENNReal.ofReal t →
        cluster (μ ω) R z t ⊆ A i ∧ A i ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen (A i) → regularizedCluster (μ ω) R z t = A i) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    ae_subharmonicBall_uniqueness_off_countable_frontier_family hI2 γ α₀ hγ hγ2 hα
      Ω P hC hcirc μ hGFF hμ] with ω hV hunique
  let : NullSingletonClass (μ ω) := ⟨fun x => by
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 (‖x‖ + 1) hR).measure_singleton hx⟩
  intro ι A hpair
  apply hunique ι A
  intro i j hij
  exact (hpair i j hij).measure_zero (μ ω)

end HarmonicBalls

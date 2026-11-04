import HarmonicBalls.Proofs.Sec5.BoundaryJumpAttachment
import HarmonicBalls.Proofs.Sec5.BoundaryJumpCount

/-! # Components of a possible boundary jump

A possible boundary jump has at most countably many connected components.
This does not rule out a nonempty boundary jump.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Function
open scoped ENNReal MeasureTheory

/-- A component of a measurable set is measurable: it is relatively closed in
that set. -/
theorem measurableSet_connectedComponentIn_of_measurable {S : Set ℂ}
    (hS : MeasurableSet S) (x : ℂ) : MeasurableSet (connectedComponentIn S x) := by
  by_cases hx : x ∈ S
  · have heq : connectedComponentIn S x = closure (connectedComponentIn S x) ∩ S := by
      apply Subset.antisymm
      · exact subset_inter subset_closure (connectedComponentIn_subset S x)
      · intro y ⟨hy, hyS⟩
        have hc : IsPreconnected (connectedComponentIn S x ∪ {y}) :=
          isPreconnected_connectedComponentIn.subset_closure subset_union_left
            (union_subset subset_closure (singleton_subset_iff.mpr hy))
        have hs : connectedComponentIn S x ∪ {y} ⊆ S :=
          union_subset (connectedComponentIn_subset S x) (singleton_subset_iff.mpr hyS)
        exact hc.subset_connectedComponentIn
          (mem_union_left _ (mem_connectedComponentIn hx)) hs (mem_union_right _ rfl)
    rw [heq]
    exact isClosed_closure.measurableSet.inter hS
  · rw [connectedComponentIn_eq_empty hx]
    exact MeasurableSet.empty

/-- A measurable subset of the unit circle has countably many components if
each component has positive one-dimensional Hausdorff measure. -/
theorem countable_components_of_positive_length {S : Set ℂ} (hS : MeasurableSet S)
    (hcircle : S ⊆ sphere (0 : ℂ) 1)
    (hpos : ∀ x ∈ S, 0 < μH[1] (connectedComponentIn S x)) :
    (connectedComponentIn S '' S).Countable := by
  let I := connectedComponentIn S '' S
  have hm (C : I) : MeasurableSet (C : Set ℂ) := by
    obtain ⟨x, _, hC⟩ := C.property
    rw [← hC]
    exact measurableSet_connectedComponentIn_of_measurable hS x
  have hd : Pairwise (Disjoint on fun C : I => (C : Set ℂ)) := by
    intro C D hne
    apply Set.disjoint_left.mpr
    intro y hyC hyD
    obtain ⟨x, hx, hC⟩ := C.property
    obtain ⟨z, hz, hD⟩ := D.property
    change y ∈ (C : Set ℂ) at hyC
    change y ∈ (D : Set ℂ) at hyD
    rw [← hC] at hyC
    rw [← hD] at hyD
    have heq : connectedComponentIn S x = connectedComponentIn S z :=
      (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyD).symm
    apply hne
    apply Subtype.ext
    exact hC.symm.trans (heq.trans hD)
  have hf : μH[1] (⋃ C : I, (C : Set ℂ)) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_mono ?_) (lt_of_le_of_lt hausdorffMeasure_one_unit_sphere_le ENNReal.ofReal_lt_top)
    intro x hx
    obtain ⟨C, hxC⟩ := mem_iUnion.mp hx
    obtain ⟨y, _, hC⟩ := C.property
    rw [← hC] at hxC
    exact hcircle (connectedComponentIn_subset S y hxC)
  have hc := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
    μH[1] hm hd hf
  have hall : {C : I | 0 < μH[1] (C : Set ℂ)} = univ := by
    ext C
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨x, hx, hC⟩ := C.property
    rw [← hC]
    exact hpos x hx
  rw [hall] at hc
  exact (countable_univ_iff.mp hc).to_set

universe u

/-- Almost surely, every possible boundary jump has at most countably many
connected components, simultaneously for every centre and positive time. -/
theorem ae_countable_boundary_jump_components
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      let S := rightClosedEnvelope (fun s => cluster (μ ω) 1 z s) t \ closure (cluster (μ ω) 1 z t)
      (connectedComponentIn S '' S).Countable := by
  filter_upwards [ae_boundary_jump_component_has_positive_length hI2 hvolume h32 h33 h34 h61 h611 h82
    γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hpos hinter
  intro t ht z hz
  apply countable_components_of_positive_length
  · exact (isClosed_rightClosedEnvelope _ _).measurableSet.diff isClosed_closure.measurableSet
  · intro y hy
    have hclosed : y ∈ closedBall (0 : ℂ) 1 :=
      (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall)
        (mem_iInter.mp hy.1 0)
    have hnot : y ∉ ball (0 : ℂ) 1 := fun hyb => hy.2 (by
      apply hinter t ht z hz
      exact ⟨by simpa only [rightClosedEnvelope, dyadicScale] using hy.1, hyb⟩)
    apply mem_sphere.mpr
    exact le_antisymm (mem_closedBall.mp hclosed)
      (le_of_not_gt (by simpa only [mem_ball] using hnot))
  · exact hpos t ht z hz

#print axioms ae_countable_boundary_jump_components
#print axioms countable_components_of_positive_length
#print axioms measurableSet_connectedComponentIn_of_measurable

end HarmonicBalls

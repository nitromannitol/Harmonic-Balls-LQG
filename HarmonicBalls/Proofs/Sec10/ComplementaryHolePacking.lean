import HarmonicBalls.Proofs.Sec10.ExteriorComponent
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Packing bounded complementary components

A locally finite measure can assign at least a fixed positive mass to only
finitely many bounded complementary components of a disk-contained closed
set. Applied to planar volume, this controls holes containing large disks. -/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter Function
open scoped ENNReal

/-- Connected components are pairwise disjoint. -/
theorem connectedComponentsIn_pairwise_disjoint {X : Type*} [TopologicalSpace X]
    (S : Set X) : (connectedComponentsIn S).PairwiseDisjoint id := by
  intro U hU V hV hne
  apply disjoint_left.mpr
  intro x hxU hxV
  obtain ⟨u, hu, rfl⟩ := hU
  obtain ⟨v, hv, rfl⟩ := hV
  exact hne ((connectedComponentIn_eq hxU).trans (connectedComponentIn_eq hxV).symm)

/-- An open subset of a separable locally connected space has only
countably many connected components. -/
theorem countable_connectedComponentsIn_of_isOpen
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [TopologicalSpace.SeparableSpace X]
    {S : Set X} (hS : IsOpen S) : (connectedComponentsIn S).Countable := by
  apply (connectedComponentsIn_pairwise_disjoint S).countable_of_isOpen
  · rintro U ⟨x, hx, rfl⟩
    exact hS.connectedComponentIn
  · rintro U ⟨x, hx, rfl⟩
    exact ⟨x, mem_connectedComponentIn hx⟩

/-- Among bounded complementary components, only finitely many have measure
at least a fixed positive value for any locally finite measure. -/
theorem finite_large_bounded_complement_components
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {K : Set ℂ}
    (hKc : IsClosed K) {r : ℝ} (hr : 0 < r) (hK : K ⊆ closedBall 0 r)
    {p : ℂ} (hp : p ∈ (closedBall (0 : ℂ) r)ᶜ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    {U : Set ℂ | U ∈ connectedComponentsIn Kᶜ ∧ Bornology.IsBounded U ∧ ε ≤ μ U}.Finite := by
  classical
  let I := {U : Set ℂ // U ∈ connectedComponentsIn Kᶜ ∧
    U ≠ connectedComponentIn Kᶜ p}
  let f : I → Set ℂ := fun i => i.1
  have hopen : ∀ i : I, IsOpen (f i) := by
    rintro ⟨U, ⟨q, hq, rfl⟩, _⟩
    exact hKc.isOpen_compl.connectedComponentIn
  have hdis : Pairwise (Disjoint on f) := by
    intro i j hij
    exact connectedComponentsIn_pairwise_disjoint Kᶜ i.2.1 j.2.1
      (fun h => hij (Subtype.ext h))
  have hsub : (⋃ i : I, f i) ⊆ closedBall 0 r := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact component_compl_subset_closedBall_of_ne_exterior hr hK hp i.2.1 i.2.2 hi
  have hfinite : μ (⋃ i : I, f i) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsCompact.measure_lt_top (μ := μ) (isCompact_closedBall (0 : ℂ) r)).ne
      (measure_mono hsub)
  have hlarge := Measure.finite_const_le_meas_of_disjoint_iUnion μ hε
    (fun i => (hopen i).measurableSet) hdis hfinite
  have himage : (Subtype.val '' {i : I | ε ≤ μ (f i)}).Finite := hlarge.image Subtype.val
  apply himage.subset
  rintro U ⟨hU, hb, hμ⟩
  have hne : U ≠ connectedComponentIn Kᶜ p := by
    intro heq
    exact not_isBounded_exterior_component hr hK hp (heq ▸ hb)
  exact ⟨⟨U, hU, hne⟩, hμ, rfl⟩

/-- A closed disk-contained planar set has only finitely many bounded
complementary components containing a disk of any given positive radius. -/
theorem finite_bounded_complement_components_containing_ball
    {K : Set ℂ} (hKc : IsClosed K) {r : ℝ} (hr : 0 < r)
    (hK : K ⊆ closedBall 0 r) {p : ℂ}
    (hp : p ∈ (closedBall (0 : ℂ) r)ᶜ) {δ : ℝ} (hδ : 0 < δ) :
    {U : Set ℂ | U ∈ connectedComponentsIn Kᶜ ∧ Bornology.IsBounded U ∧
      ∃ x : ℂ, ball x δ ⊆ U}.Finite := by
  have hpos : 0 < volume (ball (0 : ℂ) δ) := isOpen_ball.measure_pos volume
    ⟨0, mem_ball_self hδ⟩
  apply (finite_large_bounded_complement_components volume hKc hr hK hp hpos).subset
  rintro U ⟨hU, hb, x, hx⟩
  refine ⟨hU, hb, ?_⟩
  calc
    volume (ball (0 : ℂ) δ) = volume (ball x δ) := by rw [Complex.volume_ball, Complex.volume_ball]
    _ ≤ volume U := measure_mono hx

universe u

/-- On the LQG volume-growth event, for every compactly contained cluster
and every positive mass threshold, only finitely many bounded complementary
components have at least that mass. -/
theorem ae_cluster_finitely_many_large_holes
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 → ∀ ε : ℝ≥0∞, 0 < ε →
      {U : Set ℂ | U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
        Bornology.IsBounded U ∧ ε ≤ μ ω U}.Finite := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  intro t ht z hz hcl ε hε
  have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  exact finite_large_bounded_complement_components (μ ω) isClosed_closure zero_lt_one
    (hcl.trans ball_subset_closedBall) hp hε

end HarmonicBalls

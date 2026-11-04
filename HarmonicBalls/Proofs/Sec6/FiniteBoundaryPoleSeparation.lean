import HarmonicBalls.Draft.Section6

/-! # Pole separation from a finite boundary supremum

The finite-supremum condition in the harmonic-measure comparison prevents a
cluster component from accumulating at a pole outside the domain.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- If the extended odometer is bounded on the part of the boundary reached by
a set, then the set's closure avoids any pole outside the open domain. -/
theorem pole_not_mem_closure_of_boundary_odometerExt_ne_top
    {μ : Measure ℂ} {z : ℂ} {t : ℝ} {A Y : Set ℂ}
    (hA : IsOpen A) (hYA : Y ⊆ A) (hzA : z ∉ A)
    (hfinite : (⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y) ≠ ⊤) :
    z ∉ closure Y := by
  intro hzY
  have hzfront : z ∈ frontier A := by
    rw [hA.frontier_eq]
    exact ⟨closure_mono hYA hzY, hzA⟩
  have htop : (⊤ : ℝ≥0∞) ≤ ⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y := by
    calc
      ⊤ = odometerExt μ z t z := by simp [odometerExt]
      _ ≤ ⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y :=
        le_iSup_of_le z (le_iSup_of_le ⟨hzfront, hzY⟩ le_rfl)
  exact hfinite (top_le_iff.mp htop)

/-- A finite boundary supremum gives a positive-radius neighbourhood of the
pole disjoint from the closure of the relevant component. -/
theorem exists_ball_disjoint_closure_of_boundary_odometerExt_ne_top
    {μ : Measure ℂ} {z : ℂ} {t : ℝ} {A Y : Set ℂ}
    (hA : IsOpen A) (hYA : Y ⊆ A) (hzA : z ∉ A)
    (hfinite : (⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y) ≠ ⊤) :
    ∃ r : ℝ, 0 < r ∧ Disjoint (ball z r) (closure Y) := by
  have hz : z ∈ (closure Y)ᶜ :=
    pole_not_mem_closure_of_boundary_odometerExt_ne_top hA hYA hzA hfinite
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl z hz
  exact ⟨r, hr, disjoint_left.mpr fun y hy hyY => hball hy hyY⟩

/-- Cutting out a small closed disc around the pole leaves the selected
component unchanged whenever its boundary odometer supremum is finite. -/
theorem exists_pole_avoiding_domain_with_same_component
    {μ : Measure ℂ} {z : ℂ} {t : ℝ} {A G : Set ℂ} {x : ℂ}
    (hA : IsOpen A) (hzA : z ∉ A) (hx : x ∈ A ∩ G)
    (hfinite : (⨆ y ∈ frontier A ∩ closure (connectedComponentIn (A ∩ G) x),
      odometerExt μ z t y) ≠ ⊤) :
    ∃ A' : Set ℂ, IsOpen A' ∧ A' ⊆ A ∧ z ∉ closure A' ∧
      (frontier A' ∩ closure (connectedComponentIn (A ∩ G) x) ⊆
        frontier A ∩ closure (connectedComponentIn (A ∩ G) x)) ∧
      connectedComponentIn (A' ∩ G) x = connectedComponentIn (A ∩ G) x := by
  let Y := connectedComponentIn (A ∩ G) x
  have hYA : Y ⊆ A := (connectedComponentIn_subset _ _).trans inter_subset_left
  obtain ⟨r, hr, hdis⟩ :=
    exists_ball_disjoint_closure_of_boundary_odometerExt_ne_top hA hYA hzA hfinite
  let A' := A \ closedBall z (r / 2)
  have hA'o : IsOpen A' := hA.sdiff isClosed_closedBall
  have hYsub : Y ⊆ A' ∩ G := by
    intro y hy
    have hyAG := connectedComponentIn_subset (A ∩ G) x hy
    refine ⟨⟨hyAG.1, ?_⟩, hyAG.2⟩
    intro hyball
    exact disjoint_left.mp hdis
      (closedBall_subset_ball (by linarith : r / 2 < r) hyball) (subset_closure hy)
  have hA'avoid : z ∉ closure A' := by
    have hsub : closure A' ⊆ (ball z (r / 2))ᶜ := by
      apply closure_minimal _ (isClosed_compl_iff.mpr isOpen_ball)
      intro y hy hyball
      exact hy.2 (ball_subset_closedBall hyball)
    intro hz
    exact hsub hz (mem_ball_self (by linarith))
  have hfront : frontier A' ∩ closure Y ⊆ frontier A ∩ closure Y := by
    intro y hy
    have hycl : y ∈ closure A := closure_mono (show A' ⊆ A from sdiff_subset) (frontier_subset_closure hy.1)
    have hynA : y ∉ A := by
      intro hyA
      have hynn : y ∉ A' := by
        have h := hy.1
        rw [hA'o.frontier_eq] at h
        exact h.2
      have hball : y ∈ closedBall z (r / 2) := by
        by_contra hnot
        exact hynn ⟨hyA, hnot⟩
      exact disjoint_left.mp hdis
        (closedBall_subset_ball (by linarith : r / 2 < r) hball) hy.2
    exact ⟨by rw [hA.frontier_eq]; exact ⟨hycl, hynA⟩, hy.2⟩
  refine ⟨A', hA'o, sdiff_subset, hA'avoid, hfront, ?_⟩
  apply Subset.antisymm
  · exact connectedComponentIn_mono x (inter_subset_inter_left G sdiff_subset)
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) hYsub

end HarmonicBalls.Section6

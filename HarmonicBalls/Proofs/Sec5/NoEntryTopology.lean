import HarmonicBalls.Steps.Sec5.Uniqueness

/-!
# Connected-set and measure steps for the no-entry argument

A connected ball avoiding the boundary of an open set is either contained in
it or disjoint from it. If it enters an increasing family, its measure must be
paid for by the increase in the family's measure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A preconnected set which avoids the boundary of an open set either lies
inside it or is disjoint from it. -/
theorem IsPreconnected.subset_or_disjoint_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {B U : Set X}
    (hB : IsPreconnected B) (hU : IsOpen U) (hfront : Disjoint B (frontier U)) :
    B ⊆ U ∨ Disjoint B U := by
  by_cases h : Disjoint B U
  · exact Or.inr h
  · left
    apply hB.subset_of_closure_inter_subset hU (Set.not_disjoint_iff.1 h)
    intro x hx
    by_contra hxU
    have hxf : x ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hx.1, hxU⟩
    exact Set.disjoint_left.1 hfront hx.2 hxf

/-- A disjoint set entering an increasing measurable family consumes at
least its own measure. -/
theorem measure_add_le_of_disjoint_entry {μ : Measure ℂ} {B U V : Set ℂ}
    (hB : MeasurableSet B) (hdis : Disjoint U B) (hUV : U ⊆ V) (hBV : B ⊆ V) :
    μ U + μ B ≤ μ V := by
  rw [← measure_union hdis hB]
  exact measure_mono (union_subset hUV hBV)

/-- The intersection property gives an initial time at which a connected set
outside the center is disjoint from an increasing family, provided it never
meets a family boundary. -/
theorem exists_disjoint_time_of_iInter_eq_singleton
    {A : ℝ → Set ℂ} {z : ℂ} {B : Set ℂ} {t : ℝ}
    (ht : 0 < t) (hx : ∃ x ∈ B, x ≠ z)
    (hinter : ⋂ s ∈ Ioi (0 : ℝ), A s = {z})
    (hmono : MonotoneOn A (Ioi 0))
    (hdich : ∀ s : ℝ, 0 < s → s ≤ t → B ⊆ A s ∨ Disjoint B (A s)) :
    ∃ s : ℝ, 0 < s ∧ s ≤ t ∧ Disjoint B (A s) := by
  obtain ⟨x, hxB, hxz⟩ := hx
  have hex : ∃ s : ℝ, 0 < s ∧ x ∉ A s := by
    by_contra h
    have hall : x ∈ ⋂ s ∈ Ioi (0 : ℝ), A s := by
      simp only [mem_iInter, mem_Ioi]
      intro s hs
      by_contra hxs
      exact h ⟨s, hs, hxs⟩
    rw [hinter] at hall
    exact hxz (mem_singleton_iff.1 hall)
  obtain ⟨s, hs, hxs⟩ := hex
  let u := min s t
  have hu : 0 < u := lt_min hs ht
  have hut : u ≤ t := min_le_right s t
  have hus : u ≤ s := min_le_left s t
  have hxu : x ∉ A u := fun hxu => hxs (hmono hu hs hus hxu)
  rcases hdich u hu hut with hsub | hdis
  · exact False.elim (hxu (hsub hxB))
  · exact ⟨u, hu, hut, hdis⟩

/-- A ball outside the regularized cluster is initially disjoint from any
competing harmonic-ball family whose boundary stays in the cluster closure. -/
theorem exists_disjoint_time_of_cluster_boundary
    {μ : Measure ℂ} {Λ A : ℝ → Set ℂ} {z x : ℂ} {r t : ℝ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hA : IsHarmonicBallFamily μ A z)
    (hbound : ∀ s : ℝ, 0 < s → frontier (A s) ⊆ closure (Λ s))
    (ht : 0 < t) (hr : 0 < r) (haway : ball x r ⊆ (closure (Λ t))ᶜ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ t ∧ Disjoint (ball x r) (A s) := by
  have hznot : z ∉ ball x r := by
    intro hzB
    exact haway hzB (subset_closure (hΛ.1.mem t ht))
  apply exists_disjoint_time_of_iInter_eq_singleton ht
    ⟨x, mem_ball_self hr, fun hxz => hznot (hxz ▸ mem_ball_self hr)⟩
    hA.2.iInter_eq hA.2.monotoneOn
  intro s hs hst
  apply IsPreconnected.subset_or_disjoint_of_disjoint_frontier isPreconnected_ball
    (hA.2.isRegularOpen s hs).isOpen
  apply Set.disjoint_left.2
  intro y hy hyfront
  exact haway hy (closure_mono (hΛ.1.monotoneOn hs ht hst) (hbound s hs hyfront))

end HarmonicBalls

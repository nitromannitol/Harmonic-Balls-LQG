import HarmonicBalls.Proofs.Sec5.BoundaryInteriorBallContinuity

/-! # Necessity of the boundary interior-ball criterion

For decreasing open sets, a point which eventually leaves their closures
has the uniform interior-ball property. Consequently the sufficient condition
in `BoundaryInteriorBallContinuity` is also necessary for right continuity;
it must not be treated as an independently established geometric estimate.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise ENNReal

/-- If a point eventually leaves a decreasing family of open sets, then the
members whose closures still contain it have uniformly sized interior balls
in any prescribed neighbourhood of that point. -/
theorem interior_ball_of_not_mem_iInter_closure
    {B : ℕ → Set ℂ} (hanti : Antitone B) (hopen : ∀ n, IsOpen (B n))
    (hbound : ∀ n, B n ⊆ ball (0 : ℂ) 1) {x : ℂ}
    (hx : x ∉ ⋂ n, closure (B n)) {d : ℝ} (hd : 0 < d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n, x ∈ closure (B n) →
      ∃ y ∈ ball (0 : ℂ) 1, ball y ρ ⊆ B n ∩ ball x d := by
  classical
  have heach (n : ℕ) : ∃ ρ : ℝ, 0 < ρ ∧ (x ∈ closure (B n) →
      ∃ y ∈ ball (0 : ℂ) 1, ball y ρ ⊆ B n ∩ ball x d) := by
    by_cases hxn : x ∈ closure (B n)
    · obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hxn d hd
      have hyball : y ∈ ball x d := by simpa [mem_ball, dist_comm] using hyx
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp ((hopen n).inter isOpen_ball)
        y ⟨hy, hyball⟩
      exact ⟨ρ, hρ, fun _ => ⟨y, hbound n hy, hsub⟩⟩
    · exact ⟨1, zero_lt_one, fun h => (hxn h).elim⟩
  have hfinite (N : ℕ) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ n < N, x ∈ closure (B n) →
      ∃ y ∈ ball (0 : ℂ) 1, ball y ρ ⊆ B n ∩ ball x d := by
    induction N with
    | zero => exact ⟨1, zero_lt_one, by simp⟩
    | succ N ih =>
      obtain ⟨ρ₁, hρ₁, hfirst⟩ := ih
      obtain ⟨ρ₂, hρ₂, hlast⟩ := heach N
      refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
      intro n hn hxn
      by_cases hnN : n < N
      · obtain ⟨y, hy, hsub⟩ := hfirst n hnN hxn
        exact ⟨y, hy, (ball_subset_ball (min_le_left _ _)).trans hsub⟩
      · have hnEq : n = N := by omega
        subst n
        obtain ⟨y, hy, hsub⟩ := hlast hxn
        exact ⟨y, hy, (ball_subset_ball (min_le_right _ _)).trans hsub⟩
  simp only [mem_iInter, not_forall] at hx
  obtain ⟨N, hN⟩ := hx
  obtain ⟨ρ, hρ, hsmall⟩ := hfinite N
  refine ⟨ρ, hρ, ?_⟩
  intro n hxn
  by_cases hn : n < N
  · exact hsmall n hn hxn
  · exact (hN (closure_mono (hanti (Nat.le_of_not_gt hn)) hxn)).elim

/-- Right continuity forces the boundary interior-ball condition, without
volume-growth or mass assumptions. -/
theorem boundary_interior_ball_of_cluster_right_continuity
    {μ : Measure ℂ} {z : ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s')
    (hopen : ∀ n : ℕ, IsOpen (cluster μ 1 z (t + dyadicScale n)))
    (hright : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ 1 z s) ⊆ cluster μ 1 z t + ball (0 : ℂ) ε) :
    ∀ x ∈ sphere (0 : ℂ) 1, x ∉ closure (cluster μ 1 z t) →
      ∀ d : ℝ, 0 < d → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n,
        x ∈ closure (cluster μ 1 z (t + dyadicScale n)) →
        ∃ y ∈ ball (0 : ℂ) 1,
          ball y ρ ⊆ cluster μ 1 z (t + dyadicScale n) ∩ ball x d := by
  intro x _ hx d hd
  have hnot : x ∉ ⋂ n : ℕ, closure (cluster μ 1 z (t + dyadicScale n)) := by
    intro h
    exact hx ((cluster_closure_dyadic_iInter_subset_iff_right_continuous ht hmono).mpr hright h)
  apply interior_ball_of_not_mem_iInter_closure ?_ hopen (fun _ => cluster_subset_ball) hnot hd
  intro i j hij
  apply hmono _ _ (add_pos ht (dyadicScale_pos j))
  apply add_le_add le_rfl
  dsimp [dyadicScale]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij

/-- With vanishing increments and no new interior points, the boundary
interior-ball condition is equivalent to right continuity. -/
theorem cluster_right_continuity_iff_boundary_interior_ball
    {μ : Measure ℂ} {βm βp : ℝ} (hV : VolumeGrowth μ 1 βm βp)
    {z : ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s')
    (hopen : ∀ n : ℕ, IsOpen (cluster μ 1 z (t + dyadicScale n)))
    (hmass : Tendsto (fun n : ℕ => μ (cluster μ 1 z (t + dyadicScale n) \
      cluster μ 1 z t)) atTop (𝓝 0))
    (hinter : (⋂ n : ℕ, closure (cluster μ 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
      closure (cluster μ 1 z t)) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ 1 z s) ⊆ cluster μ 1 z t + ball (0 : ℂ) ε) ↔
    (∀ x ∈ sphere (0 : ℂ) 1, x ∉ closure (cluster μ 1 z t) →
      ∀ d : ℝ, 0 < d → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n,
        x ∈ closure (cluster μ 1 z (t + dyadicScale n)) →
        ∃ y ∈ ball (0 : ℂ) 1,
          ball y ρ ⊆ cluster μ 1 z (t + dyadicScale n) ∩ ball x d) := by
  constructor
  · exact boundary_interior_ball_of_cluster_right_continuity ht hmono hopen
  · exact cluster_right_continuity_of_boundary_interior_ball hV ht hmono hmass hinter


end HarmonicBalls

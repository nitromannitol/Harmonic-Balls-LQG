import HarmonicBalls.Proofs.Sec5.OpenBoundaryJumpModel
import HarmonicBalls.Proofs.Sec5.InteriorHausdorffContinuity

/-! # Interior continuity and boundary contact

A geometric model separates compact-interior continuity from continuity on
closure. It is not an LQG obstacle-problem solution.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise ENNReal

/-- There is an increasing family of open connected subsets of the unit disc
whose increment area tends to zero and which is right-continuous on every
closed interior set, but is not right-continuous on the whole closure. -/
theorem exists_open_connected_local_continuity_but_boundary_jump :
    ∃ F : ℝ → Set ℂ,
      (∀ t, IsOpen (F t) ∧ IsConnected (F t) ∧ F t ⊆ ball (0 : ℂ) 1) ∧
      Monotone F ∧
      Tendsto (fun n : ℕ => volume (F (1 + (2 : ℝ)⁻¹ ^ n) \ F 1)) atTop (𝓝 0) ∧
      (∀ K : Set ℂ, IsClosed K → K ⊆ ball (0 : ℂ) 1 → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 1 (1 + δ),
          closure (F s) ∩ K ⊆ F 1 + ball (0 : ℂ) ε) ∧
      ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 1 (1 + δ),
        closure (F s) ⊆ F 1 + ball (0 : ℂ) ε := by
  obtain ⟨F, hF, hm, hmass, hboundary, _, hne⟩ :=
    exists_open_connected_zero_area_boundary_jump
  have hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s' := fun _ _ _ h => hm h
  have hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1 := fun s _ => (hF s).2.2
  have hinter : (⋂ n : ℕ, closure (F (1 + dyadicScale n))) ∩ ball (0 : ℂ) 1 ⊆
      closure (F 1) := by
    intro x hx
    by_contra hnot
    have hsphere := hboundary ⟨by simpa [rightClosedEnvelope, dyadicScale] using hx.1, hnot⟩
    have hdlt : dist x (0 : ℂ) < 1 := mem_ball.mp hx.2
    have hdeq : dist x (0 : ℂ) = 1 := mem_sphere.mp hsphere
    linarith
  refine ⟨F, hF, hm, hmass, ?_, ?_⟩
  · intro K hK hKsub ε hε
    exact local_right_continuity_of_no_new_interior_points zero_lt_one hmono hbound hinter
      hK hKsub hε
  · intro hcont
    have hsub := (closure_dyadic_iInter_subset_iff_right_continuous zero_lt_one hmono hbound).2 hcont
    obtain ⟨x, hx, hnot⟩ := hne
    exact hnot (hsub (by simpa [rightClosedEnvelope, dyadicScale] using hx))

end HarmonicBalls

import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Geometric preconditions of N2 from the buffered pinch geometry

The two geometric hypotheses of the exterior annular Green potential lemma (`hsph` and `hWA` of
`exists_exterior_annulusGreenPotentialSup_of_frozen_holder`, `FirstPass/S11p/ExteriorMass.lean`) are consequences of the
fixed buffered keyhole geometry `IsBufferedPinchGeometry` (`FirstPass/S11h/Faithful.lean`; corrected paper lines 3157-3201):

* `closure W ⊆ T ⊆ 𝔸_{1,5}`, so the unit circle `∂B₁` avoids `closure W` (`sphere_one_subset_compl_closure_W_of_buffered`);
* `W ⊆ 𝔸_{1,2}`, so `closure W ⊆ closedBall 0 2`, which avoids the closed annulus `{3 ≤ |z| ≤ 6}` containing the closure of
  every open `U ⊆ 𝔸_{3,6}` (`closure_annulus_compl_closure_W_of_buffered`).

Both are pure set-geometry facts; no probability is involved.
-/

namespace HarmonicBalls

open Metric Set

/-- The unit circle avoids the closure of `W`: `closure W ⊆ T ⊆ 𝔸_{1,5}` and `∂B₁ ⊆ closedBall 0 1`. -/
theorem sphere_one_subset_compl_closure_W_of_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ := by
  intro z hz hzW
  have hA : z ∈ annulus (0 : ℂ) 1 5 := h.T_subset (h.closure_W_subset_T hzW)
  exact hA.2 (sphere_subset_closedBall hz)

/-- Every open `U ⊆ 𝔸_{3,6}` has closure avoiding `closure W`: `closure W ⊆ closedBall 0 2` and `closure U ⊆ {3 ≤ |z|}`. -/
theorem closure_annulus_compl_closure_W_of_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∀ A : Set ℂ, IsOpen A → A ⊆ annulus (0 : ℂ) 3 6 → closure A ⊆ (closure W)ᶜ := by
  intro A _ hA z hzA hzW
  have hWb : W ⊆ closedBall (0 : ℂ) 2 := fun w hw => ball_subset_closedBall (h.W_subset hw).1
  have hcW : closure W ⊆ closedBall (0 : ℂ) 2 := closure_minimal hWb isClosed_closedBall
  have hcA : closure A ⊆ {w : ℂ | 3 ≤ ‖w‖} := by
    refine closure_minimal (fun w hw => ?_) (isClosed_le continuous_const continuous_norm)
    have hw' : w ∉ closedBall (0 : ℂ) 3 := (hA hw).2
    rw [mem_closedBall, dist_zero_right, not_le] at hw'
    exact le_of_lt hw'
  have h1 : ‖z‖ ≤ 2 := by simpa [mem_closedBall, dist_zero_right] using hcW hzW
  have h2 : 3 ≤ ‖z‖ := hcA hzA
  linarith

end HarmonicBalls

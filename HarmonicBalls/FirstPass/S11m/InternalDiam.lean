import HarmonicBalls.FirstPass.S11h.OuterDiamFinite
import HarmonicBalls.Proofs.Sec11.PlanarDiskRemoval

/-!
# Finiteness of the first-event diameter `d₀`

Route: finiteness of `d₀` used for `P(F) > 0`, for the
set `K₀ = closure (T \ B_{3δ}(W))` of the local first event (`pinchFirstEventLocal`, `FirstPass/S11h/LocalEvents.lean`;
corrected paper lines 3603-3608). `W = B_ρ(c)` is a disk (concentric clause), `closedBall c (ρ + 3δ) ⊆ T` (buffer_W),
and removing that open disk from the connected open set `T` leaves a connected set
(`isConnected_sdiff_ball_of_closure_subset`). No external input.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The diameter `d₀ = diam^δ_D(K₀)`, `K₀ = closure (T \ B_{3δ}(W))`, of the local first event is finite for every
Euclidean length metric `D` (route section 6.2). -/
theorem IsBufferedPinchGeometry.internalDiam_K0_lt_top {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    internalDiam D δ (closure (T \ thickening (3 * δ) W)) < ⊤ := by
  obtain ⟨c, ρU, ρV, ρW, -, -, hWc⟩ := hgeo.concentric
  have hδ : 0 < δ := hgeo.delta_pos
  have h10 : (0 : ℝ) < 10 * δ := by linarith
  have h3 : (0 : ℝ) < 3 * δ := by linarith
  -- U ⊆ V ⊆ W by the buffer conditions, so W is nonempty and its radius is positive
  have hUV : U ⊆ V := fun x hx =>
    hgeo.buffer_U (subset_closure (self_subset_thickening h10 _ (subset_closure hx)))
  have hVW : V ⊆ W := fun x hx =>
    hgeo.buffer_V (subset_closure (self_subset_thickening h10 _ (subset_closure hx)))
  obtain ⟨x, hx⟩ := hgeo.U_nonempty
  have hρW : 0 < ρW := by
    have hne : (ball c ρW).Nonempty := by
      rw [← hWc]
      exact ⟨x, hVW (hUV hx)⟩
    exact Metric.nonempty_ball.mp hne
  have hr : (0 : ℝ) < 3 * δ + ρW := by linarith
  have hthick : thickening (3 * δ) W = ball c (3 * δ + ρW) := by
    rw [hWc, thickening_ball h3 hρW]
  -- the closed disk of radius 3δ + ρW lies in T: it is the 3δ-cthickening of closure W
  have hWcl : closedBall c ρW = closure W := by
    rw [hWc, closure_ball c hρW.ne']
  have hcl : closedBall c (3 * δ + ρW) = cthickening (3 * δ) (closure W) := by
    rw [← hWcl, cthickening_closedBall h3.le hρW.le]
  have hdisk : closure (ball c (3 * δ + ρW)) ⊆ T := by
    rw [closure_ball c hr.ne', hcl]
    intro z hz
    have hz' : z ∈ thickening (10 * δ) (closure W) :=
      cthickening_subset_thickening' h10 (by linarith) _ hz
    exact (hgeo.buffer_W (subset_closure hz')).1
  -- T is bounded, hence so are its subsets and their closures
  have hbdd : Bornology.IsBounded T := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 6)).subset ?_
    intro z hz
    have h6 := hgeo.closure_T_subset (subset_closure hz)
    simp only [annulus, mem_sdiff] at h6
    exact ball_subset_closedBall h6.1
  have hbddK : Bornology.IsBounded (closure (T \ ball c (3 * δ + ρW))) :=
    (hbdd.subset sdiff_subset).closure
  have hconn : IsConnected (closure (T \ ball c (3 * δ + ρW))) :=
    (isConnected_sdiff_ball_of_closure_subset hgeo.isOpen_T hgeo.isConnected_T c hr hdisk).closure
  rw [hthick]
  exact hD.internalDiam_lt_top_of_connected_thickening hD.nonneg_apply hδ hbddK
    (IsConnected.thickening_complex hconn hδ)

end HarmonicBalls

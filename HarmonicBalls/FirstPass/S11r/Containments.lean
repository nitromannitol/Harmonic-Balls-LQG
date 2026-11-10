import HarmonicBalls.FirstPass.S11i.HzoomUnitBallFit
import HarmonicBalls.FirstPass.S11al
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Containments of the buffered pinch geometry (fp-S11r-G-data, n2)

Both containment inputs of the ball-metric instance follow from `IsBufferedPinchGeometry` (S11h/Faithful.lean), so they
are no longer binders:
* `hU : U ⊆ closedBall 0 7` is `FirstPassS11iHzoomUnitBallFit.subset_closedBall_of_buffered` (reused as `hU_of_buffered`);
* `hCont : CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q` (S11al.lean) is
  `certificateContainments_of_buffered`, from the buffer conditions `buffer_T`, `buffer_V`, `buffer_W`, `buffer_Q'`,
  `buffer_Q` at the radius `10 δ` (the radii `δ`, `4δ`, `3δ`, `2δ` of the containments are at most `10 δ`) and from
  `delta_lt : δ < 1/1000`.
-/

open Metric Set

namespace HarmonicBalls.FirstPassS11rContainments

/-- Thickenings are monotone in the radius and in the set. -/
lemma thickening_mono_set {A B : Set ℂ} {r s : ℝ} (hr : r ≤ s) (hAB : A ⊆ B) :
    thickening r A ⊆ thickening s B := by
  intro x hx
  obtain ⟨z, hz, hd⟩ := Metric.mem_thickening_iff.1 hx
  exact Metric.mem_thickening_iff.2 ⟨z, hAB hz, lt_of_lt_of_le hd hr⟩

/-- An annulus `𝔸_{a,b}(0) = B_b(0) \ closedBall 0 a` with outer radius at most `7` lies in `closedBall 0 7`. -/
lemma annulus_subset_closedBall {a b : ℝ} (hb : b ≤ 7) : annulus 0 a b ⊆ closedBall (0 : ℂ) 7 :=
  fun _ hx => closedBall_subset_closedBall hb (ball_subset_closedBall hx.1)

/-- `hU` of the ball-metric instance: the root disc of a buffered pinch geometry lies in `closedBall 0 7`. -/
theorem hU_of_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ) : U ⊆ closedBall (0 : ℂ) 7 :=
  HarmonicBalls.FirstPassS11iHzoomUnitBallFit.subset_closedBall_of_buffered hgeo

/-- `hCont` of the ball-metric instance: the certificate containments of the buffered pinch geometry, with the
deterministic component `pinchOmegaGeom W Q δ` as the open set `Ostar`. -/
theorem certificateContainments_of_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ) :
    FirstPassS11i.CertificateContainments δ (HarmonicBalls.pinchOmegaGeom W Q δ) V W T Q' Q := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hδ1 : δ < 1 / 1000 := hgeo.delta_lt
  have hTb : thickening (10 * δ) (closure T) ⊆ closedBall (0 : ℂ) 7 :=
    fun x hx => annulus_subset_closedBall (by norm_num) (hgeo.buffer_T (subset_closure hx))
  have hVb : thickening (10 * δ) (closure V) ⊆ closedBall (0 : ℂ) 7 :=
    fun x hx => annulus_subset_closedBall (by norm_num) (hgeo.W_subset (hgeo.buffer_V (subset_closure hx)))
  have hWb : thickening (10 * δ) (closure W) ⊆ closedBall (0 : ℂ) 7 :=
    fun x hx => annulus_subset_closedBall (by norm_num) (hgeo.buffer_W (subset_closure hx)).2
  have hQb : Q ⊆ closedBall (0 : ℂ) 7 :=
    fun x hx => annulus_subset_closedBall (by norm_num) (hgeo.closure_Q_subset (subset_closure hx)).1
  refine
    { eta_pos := hδ
      three_eta_le := by linarith
      Ostar_sub := by
        intro x hx
        unfold HarmonicBalls.pinchOmegaGeom at hx
        exact ball_subset_closedBall ((connectedComponentIn_subset _ _ hx).1)
      Qprime_sub := fun x hx => hQb (hgeo.closure_Q'_subset_Q (subset_closure hx))
      Q_sub := hQb
      T_thick := fun x hx => hTb (thickening_mono_set (by linarith) (fun y hy => subset_closure hy) hx)
      V_thick := fun x hx => hVb (thickening_mono_set (by linarith) (fun y hy => subset_closure hy) hx)
      W_thick := fun x hx => hWb (thickening_mono_set (by linarith) (fun y hy => subset_closure hy) hx) }

end HarmonicBalls.FirstPassS11rContainments

#print axioms HarmonicBalls.FirstPassS11rContainments.certificateContainments_of_buffered
#print axioms HarmonicBalls.FirstPassS11rContainments.hU_of_buffered

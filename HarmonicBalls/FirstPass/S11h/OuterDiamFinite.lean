import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.Steps.Sec11.PinchAnnulusConnected

/-!
# Section 11: finiteness of the outer internal diameter

Deterministic input `d₂ < ∞` of Lemma 11.17 (`lemma:third-event-proof`, corrected paper lines 3726-3756). The
diameter `d₂ = diam^{δ}_D(B_{3δ}(W) \ V)` is the one in the event `Ẽ₃` (`pinchThirdEvent`, `Draft/Section11.lean:107`).

For a Euclidean length metric `D` and concentric disks `V = B(c, ρV)`, `W = B(c, ρW)` (`IsBufferedPinchGeometry.concentric`)
the set `B_{3δ}(W) \ V` is empty, a disk, or a concentric annulus. Its positive thickening is connected and the set is
bounded, so the finiteness lemma `IsEuclideanLengthMetric.internalDiam_lt_top_of_connected_thickening`
(`Steps/Sec11/PinchDiameterFiniteness.lean:53`) applies. No inclusion `V ⊆ W` is used.

The helpers are reused from `Steps/Sec11/PinchAnnulusConnected.lean`: `IsConnected.thickening_complex` and
`isConnected_ball_sdiff_ball_complex`. Nothing here is a hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- A Euclidean length metric is nonnegative: `2 D(x,y) = D(x,y) + D(y,x) ≥ D(x,x) = 0`. -/
theorem IsEuclideanLengthMetric.nonneg_apply {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- For a Euclidean length metric `D`, the internal diameter `diam^δ_D(B_{3δ}(B(c, b)) \ B(c, a))` is finite, for all
real radii `a, b` (the annulus of the corrected paper's third event, with `a = ρV`, `b = ρW`). -/
theorem internalDiam_thickening_ball_sdiff_ball_lt_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) (c : ℂ) (a b : ℝ) :
    internalDiam D δ (thickening (3 * δ) (ball c b) \ ball c a) < ⊤ := by
  have hnonneg : ∀ x y, 0 ≤ D x y := hD.nonneg_apply
  by_cases hb : b ≤ 0
  · rw [ball_eq_empty.mpr hb, thickening_empty, empty_sdiff]
    simp [internalDiam]
  · have hb0 : 0 < b := not_le.mp hb
    rw [thickening_ball (by linarith : (0 : ℝ) < 3 * δ) hb0]
    by_cases ha : a ≤ 0
    · rw [ball_eq_empty.mpr ha, sdiff_empty]
      exact hD.internalDiam_lt_top_of_connected_thickening hnonneg hδ isBounded_ball
        (IsConnected.thickening_complex
          ((convex_ball c (3 * δ + b)).isConnected ⟨c, mem_ball_self (by linarith)⟩) hδ)
    · have ha0 : 0 < a := not_le.mp ha
      by_cases hab : 3 * δ + b ≤ a
      · rw [sdiff_eq_empty.mpr (ball_subset_ball hab)]
        simp [internalDiam]
      · have hab0 : a < 3 * δ + b := not_le.mp hab
        have hconn : IsConnected (ball c (3 * δ + b) \ ball c a) :=
          isConnected_ball_sdiff_ball_complex c ha0 hab0
        exact hD.internalDiam_lt_top_of_connected_thickening hnonneg hδ
          (isBounded_ball.subset sdiff_subset) (IsConnected.thickening_complex hconn hδ)

/-- The third-event diameter `diam^δ_D(B_{3δ}(W) \ V)` of a buffered pinch geometry is finite for every Euclidean
length metric `D` (the finiteness of `d₂` in Lemma 11.17, corrected paper lines 3726-3756). -/
theorem IsBufferedPinchGeometry.internalDiam_third_lt_top {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    internalDiam D δ (thickening (3 * δ) W \ V) < ⊤ := by
  obtain ⟨c, ρU, ρV, ρW, -, hV, hW⟩ := hgeo.concentric
  rw [hV, hW]
  exact internalDiam_thickening_ball_sdiff_ball_lt_top hD hgeo.delta_pos c ρV ρW

/-- Almost surely, `d₂ < ∞` for the LQG metric of a field: the metric is a Euclidean length metric almost surely. -/
theorem ae_internalDiam_third_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∀ᵐ ω ∂P, internalDiam (D ω) δ (thickening (3 * δ) W \ V) < ⊤ :=
  hD.mono fun _ h => hgeo.internalDiam_third_lt_top h


end HarmonicBalls

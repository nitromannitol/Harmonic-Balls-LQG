import HarmonicBalls.FirstPass.S11j.C42Six
import HarmonicBalls.Steps.Sec11.PinchConstrainedFiniteness
import HarmonicBalls.Steps.Sec11.PinchDiameterFiniteness
import HarmonicBalls.Steps.Sec11.PinchAnnulusConnected

/-!
# Almost sure finiteness of the thresholds X2 and X4 of Lemma 11.15

Both finiteness facts (paper lines 3664-3667) are deterministic consequences of the buffered geometry and of a length
metric `D` inducing the Euclidean topology (`IsEuclideanLengthMetric`); no literature input is used.

* X2, the radius-six corridor: `O = B_6 \ (closure B_{2δ}(Q) ∪ closure B_{2δ}(W))`. The component of `0` in `O` contains
  `∂B_5` (`IsBufferedPinchGeometry.sphere_subset_connectedComponentIn_six`, `FirstPass/S11j/C42Six.lean`), so the
  supremum of the internal distances from `0` to `∂B_5` is finite on that open connected component (compact set in a
  connected open set; `IsEuclideanLengthMetric.iSup_internalMetric_lt_top_of_isCompact`), and the internal metric of `O`
  is at most that of the component.
* X4, the outer piece `T \ B_{3δ}(W)`: connected (`IsBufferedPinchGeometry.isConnected_outer_piece`), bounded
  (`T ⊆ annulus 0 1 5`), so the internal diameter with respect to its connected `δ`-thickening is finite
  (`IsEuclideanLengthMetric.internalDiam_lt_top_of_connected_thickening`).

Terminology: internal metric `D(z, w; U)` and internal diameter `diam^δ` (Armitage-Gardiner for the domain; Bou-Rabee and
Gwynne, `Defs/LQGMetric.lean`, `Draft/Section11.lean`). All facts used are existing repository results (reuse first).
-/

namespace HarmonicBalls

open Set Metric Filter MeasureTheory
open scoped ENNReal

/-- Threshold X2 (radius-six corridor): for a length metric `D` inducing the Euclidean topology with nonnegative values,
the supremum of the internal distances from `0` to the sphere of radius `5` in the corridor is finite. -/
theorem IsBufferedPinchGeometry.iSup_sphere_internalMetric_lt_top {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) :
    (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D
      (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) < ⊤ := by
  have hz0 : (0 : ℂ) ∈ connectedComponentIn
      (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 :=
    h.zero_union_sphere_subset_six (Or.inl rfl)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)) :=
    connectedComponentIn_nonempty_iff.mp ⟨0, hz0⟩
  have hOo : IsOpen (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) :=
    isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hU := hOo.connectedComponentIn (x := (0 : ℂ))
  have hconn := isConnected_connectedComponentIn_iff.mpr h0
  have hfin := hD.iSup_internalMetric_lt_top_of_isCompact hnonneg hU hconn (isCompact_sphere (0 : ℂ) 5)
    h.sphere_subset_connectedComponentIn_six (mem_connectedComponentIn h0)
  exact lt_of_le_of_lt
    (iSup₂_mono fun y _ => internalMetric_anti D (connectedComponentIn_subset _ _) 0 y) hfin

/-- Threshold X4 (outer piece): the internal diameter of `T \ B_{3δ}(W)` is finite. -/
theorem IsBufferedPinchGeometry.internalDiam_outer_lt_top {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) :
    internalDiam D δ (T \ thickening (3 * δ) W) < ⊤ := by
  have hbdd : Bornology.IsBounded (T \ thickening (3 * δ) W) :=
    (Metric.isBounded_ball (x := (0 : ℂ)) (r := 5)).subset fun z hz =>
      mem_ball.mpr (mem_annulus_zero.mp (h.T_subset hz.1)).2
  exact hD.internalDiam_lt_top_of_connected_thickening hnonneg h.delta_pos hbdd
    (IsConnected.thickening_complex h.isConnected_outer_piece h.delta_pos)

/-- Almost surely, the radius-six corridor threshold X2 is finite (paper lines 3664-3667). -/
theorem ae_iSup_sphere_internalMetric_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) (hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∀ᵐ ω ∂P, (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω)
      (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) < ⊤ := by
  filter_upwards [hD, hnn] with ω h1 h2
  exact h.iSup_sphere_internalMetric_lt_top h1 h2

/-- Almost surely, the outer-piece threshold X4 is finite (paper lines 3664-3667). -/
theorem ae_internalDiam_outer_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) (hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∀ᵐ ω ∂P, internalDiam (D ω) δ (T \ thickening (3 * δ) W) < ⊤ := by
  filter_upwards [hD, hnn] with ω h1 h2
  exact h.internalDiam_outer_lt_top h1 h2


end HarmonicBalls

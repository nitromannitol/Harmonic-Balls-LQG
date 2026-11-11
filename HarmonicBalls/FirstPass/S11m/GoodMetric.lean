import HarmonicBalls.FirstPass.S11m.Finiteness
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Positivity and finiteness of the local quantities of the first event

Route: paper `lem:E1`
(`paper/lqg_harmonic_ball-corrected.tex`, lines 3661-3700). Deterministic: for a Euclidean length metric `D`,
the quantities `L = D(Q̄', ∂Q)`, `a₀ = D(0, ∂B_δ)` are strictly positive and `A = sup_{x∈∂B₅} D(0,x; Ω)` is finite,
provided the sphere `∂B₅` lies in the component `Ω = pinchOmegaGeom` of `0`.

The clause `{0} ∪ ∂B₅ ⊆ Ω` is paper lines 3186-3199 but is NOT a field of `IsBufferedPinchGeometry`; it is taken here
as the explicit hypothesis `hΩ` (gap report, see `pinchLocalA_lt_top`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- A nonempty closed bounded subset of `ℂ` other than `ℂ` has nonempty frontier. -/
theorem frontier_nonempty_of_bounded_open {Q : Set ℂ} {R : ℝ} (hQne : Q.Nonempty)
    (hQb : Q ⊆ ball (0 : ℂ) R) : (frontier Q).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hcl : IsClopen Q := isClopen_iff_frontier_eq_empty.2 h
  have huniv : Q = univ := hcl.eq_univ hQne
  have hmem : ((|R| + 1 : ℝ) : ℂ) ∈ Q := by rw [huniv]; exact mem_univ _
  have h1 := hQb hmem
  rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [abs_nonneg R])] at h1
  linarith [le_abs_self R]

/-- The minimum of a continuous nonnegative metric over two disjoint nonempty compact sets is attained, hence positive. -/
theorem setDist_pos_of_isCompact {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B) :
    0 < setDist D A B := by
  have hcont : Continuous fun p : ℂ × ℂ => D p.1 p.2 := hD.continuous_pair
  have himg : image2 D A B = (fun p : ℂ × ℂ => D p.1 p.2) '' (A ×ˢ B) := by
    ext c
    simp [mem_image2]
  have hK : IsCompact (image2 D A B) := by
    rw [himg]; exact (hA.prod hB).image hcont
  have hmem : setDist D A B ∈ image2 D A B := hK.sInf_mem (hAne.image2 hBne)
  obtain ⟨a, ha, b, hb, hab⟩ := mem_image2.1 hmem
  have hne : a ≠ b := fun h => Set.disjoint_left.1 hdisj ha (by rw [h]; exact hb)
  have hpos : 0 < D a b :=
    lt_of_le_of_ne (HarmonicBalls.S11m.isEuclideanLengthMetric_nonneg hD a b) fun h0 => hne (hD.eq_of_eq_zero a b h0.symm)
  rw [← hab]
  exact hpos

/-- `L = D(Q̄', ∂Q) > 0` for a Euclidean length metric and a buffered pinch geometry (paper `lem:E1`, `L`). -/
theorem pinchLocalL_pos {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) : 0 < pinchLocalL D Q' Q := by
  have hclQb : closure Q ⊆ ball (0 : ℂ) 5 := fun z hz =>
    ((hgeo.closure_Q_subset hz).1 : z ∈ ball (0 : ℂ) 5 \ closedBall (0 : ℂ) 4).1
  have hQb : Q ⊆ ball (0 : ℂ) 5 := subset_closure.trans hclQb
  have hbdd5 : Bornology.IsBounded (ball (0 : ℂ) 5) := Metric.isBounded_ball
  have hA : IsCompact (closure Q') :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (hbdd5.subset (hgeo.closure_Q'_subset_Q.trans hQb))
  have hB : IsCompact (frontier Q) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier (hbdd5.subset (frontier_subset_closure.trans hclQb))
  have hQne : Q.Nonempty :=
    Set.Nonempty.mono (subset_closure.trans hgeo.closure_Q'_subset_Q) hgeo.isConnected_Q'.nonempty
  have hdisj : Disjoint (closure Q') (frontier Q) :=
    Set.disjoint_left.2 fun x hx hfx =>
      hfx.2 (by rw [hgeo.isOpen_Q.interior_eq]; exact hgeo.closure_Q'_subset_Q hx)
  exact setDist_pos_of_isCompact hD hA hB hgeo.isConnected_Q'.nonempty.closure
    (frontier_nonempty_of_bounded_open hQne hQb) hdisj

/-- `a₀ = D(0, ∂B_δ) > 0` for a Euclidean length metric (the `a₀` of `pinchFirstEventLocal`). -/
theorem setDist_zero_sphere_pos {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) : 0 < setDist D {0} (sphere (0 : ℂ) δ) := by
  have hδ : 0 < δ := hgeo.delta_pos
  refine setDist_pos_of_isCompact hD isCompact_singleton (isCompact_sphere _ _) (singleton_nonempty _)
    ⟨(δ : ℂ), by simp [abs_of_pos hδ]⟩ ?_
  refine Set.disjoint_singleton_left.2 fun h => ?_
  rw [mem_sphere_zero_iff_norm, norm_zero] at h
  linarith

/-- `A = sup_{x ∈ ∂B₅} D(0, x; Ω) < ∞` for a Euclidean length metric, when `{0} ∪ ∂B₅ ⊆ Ω = pinchOmegaGeom`
(paper lines 3186-3199; the clause `hΩ` is not a field of `IsBufferedPinchGeometry`, see the gap report). The component
`Ω` is open and connected, and `IsEuclideanLengthMetric.iSup_internalMetric_lt_top_of_isCompact` bounds the sup over the
compact sphere. -/
theorem pinchLocalA_lt_top {W Q : Set ℂ} {δ : ℝ}
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hΩ : insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) : pinchLocalA D W Q δ < ⊤ := by
  have h0 : (0 : ℂ) ∈ pinchOmegaGeom W Q δ := hΩ (mem_insert _ _)
  have hS : IsOpen (ball (0 : ℂ) 7 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) :=
    isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hO : IsOpen (pinchOmegaGeom W Q δ) := hS.connectedComponentIn
  have hOc : IsConnected (pinchOmegaGeom W Q δ) := isConnected_connectedComponentIn_iff.2 (connectedComponentIn_subset _ _ h0)
  have hsph : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ := fun x hx => hΩ (mem_insert_of_mem _ hx)
  exact hD.iSup_internalMetric_lt_top_of_isCompact (HarmonicBalls.S11m.isEuclideanLengthMetric_nonneg hD) hO hOc
    (isCompact_sphere _ _) hsph h0

end HarmonicBalls

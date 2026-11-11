import HarmonicBalls.FirstPass.S11m.InternalDiam
import HarmonicBalls.FirstPass.S11m.GoodMetric
import HarmonicBalls.FirstPass.S11m.Exhaustion

/-!
# Positive probability of the good box `F` of the first local event

Route: by countable exhaustion there are thresholds
`n` with `P{L ≥ 1/(n+1), A ≤ n, D(0,∂B_{δ/2}) ≥ 1/(n+1), d₀ ≤ n} > 0`, where `L = D(Q̄', ∂Q)`,
`A = sup_{∂B₅} D(0,·; Ω_geom)`, `d₀ = diam^δ_D(K₀)`. Inputs: a.s. Euclidean length metric (hypothesis), and the clause
`{0} ∪ ∂B₅ ⊆ Ω_geom` (hypothesis `hΩ`, not a field of `IsBufferedPinchGeometry`).
No external input beyond these hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- `D(0, ∂B_r) > 0` for a Euclidean length metric `D` and `r > 0` (the disk `{0}` and the circle are disjoint compact
sets). -/
theorem setDist_zero_sphere_pos_of_pos {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {r : ℝ} (hr : 0 < r) :
    0 < setDist D {0} (sphere (0 : ℂ) r) := by
  refine setDist_pos_of_isCompact hD isCompact_singleton (isCompact_sphere _ _) (singleton_nonempty _)
    ⟨(r : ℂ), by simp [abs_of_pos hr]⟩ ?_
  refine Set.disjoint_singleton_left.2 fun h => ?_
  rw [mem_sphere_zero_iff_norm, norm_zero] at h
  linarith

/-- Countable exhaustion of the good box `F` (route section 6.2): for a.s. Euclidean length metrics `D ω` there is an
index `n` such that the event `{L ≥ 1/(n+1), A ≤ n, D(0,∂B_{δ/2}) ≥ 1/(n+1), d₀ ≤ n}` has positive (outer) probability. -/
theorem exists_pinch_F_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (D : Ω → ℂ → ℂ → ℝ) (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ n : ℕ, 0 < P {ω | 1 / ((n : ℝ) + 1) ≤ pinchLocalL (D ω) Q' Q ∧
      pinchLocalA (D ω) W Q δ ≤ (n : ℝ≥0∞) ∧
      1 / ((n : ℝ) + 1) ≤ setDist (D ω) {0} (sphere (0 : ℂ) (δ / 2)) ∧
      internalDiam (D ω) δ (closure (T \ thickening (3 * δ) W)) ≤ (n : ℝ≥0∞)} := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hgood : ∀ᵐ ω ∂P, 0 < pinchLocalL (D ω) Q' Q ∧ pinchLocalA (D ω) W Q δ < ⊤ ∧
      0 < setDist (D ω) {0} (sphere (0 : ℂ) (δ / 2)) ∧
      internalDiam (D ω) δ (closure (T \ thickening (3 * δ) W)) < ⊤ := by
    filter_upwards [hD] with ω hω
    exact ⟨pinchLocalL_pos hgeo hω, pinchLocalA_lt_top hω hΩ,
      setDist_zero_sphere_pos_of_pos hω (half_pos hδ), hgeo.internalDiam_K0_lt_top hω⟩
  exact exists_pos_measure_exhaustion P (fun ω => pinchLocalL (D ω) Q' Q)
    (fun ω => setDist (D ω) {0} (sphere (0 : ℂ) (δ / 2)))
    (fun ω => pinchLocalA (D ω) W Q δ)
    (fun ω => internalDiam (D ω) δ (closure (T \ thickening (3 * δ) W))) hgood

end HarmonicBalls

import HarmonicBalls.FirstPass.S11y.ShiftLength
import HarmonicBalls.FirstPass.S11y.ShiftGeom
import HarmonicBalls.FirstPass.S11ad.Third

/-!
# The shift for `E₃` keeps `E₁ ∩ E₂` (note §6.4)

Given a measurable set `A` on which `E₁` and `E₂` hold and `P A > 0`, choose `c, d > 0` with `a₂ ≥ c`, `d₂ ≤ d` on a
subset of positive probability (`pinch_third_const_ae`), then the bump weight `u = ξ⁻¹ log k φ` with
`k = min {1, c/(2d)}` (`S11y.exists_pinchShift_bump` for `φ`). By `S11y.pinchLocal_E3_of_shift_bump`, `E₁`, `E₂`
(for the shifted measure `μ.withDensity (exp (γ u))`) and `E₃` hold for the shifted metric, so the shifted event has
positive probability. The weight `u` is returned with its Cameron-Martin properties: smooth, compact support, and
zero average on the unit circle (`φ` vanishes on `∂B₁`, since `thickening (6δ) W` avoids `∂B₁` by `buffer_W`).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls
namespace S11ad

/-- The bump weight of a pinch shift: `f = ξ⁻¹ log k φ` for `0 < k ≤ 1` and `φ` the bump of
`S11y.exists_pinchShift_bump` (`1` on `closure (thickening δ K₂)`, `0` on `closure U`, supported in
`thickening (6δ) W`). -/
def E3ShiftSet (U V W : Set ℂ) (δ ξ : ℝ) : Set (ℂ → ℝ) :=
  {f | ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    (∀ z, φ z ∈ Icc (0 : ℝ) 1) ∧ (∀ z ∈ closure (thickening δ (S11y.pinchK2 W V δ)), φ z = 1) ∧
    (∀ z ∈ closure U, φ z = 0) ∧ (∀ z, z ∉ thickening (6 * δ) W → φ z = 0) ∧
    f = S11y.shiftWeight3 ξ k φ}

/-- The bump of `exists_pinchShift_bump` vanishes on the unit circle: `thickening (6δ) W` avoids `∂B₁`, because
`buffer_W` puts the `10δ`-thickening of `closure W` inside `annulus 0 1 2`. -/
lemma pinch_bump_vanish_sphere {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {z : ℂ} (hz : ‖z‖ = 1) : z ∉ thickening (6 * δ) W := by
  intro h
  have h1 : z ∈ thickening (10 * δ) (closure W) :=
    thickening_subset_of_subset (10 * δ) subset_closure
      (thickening_mono (show 6 * δ ≤ 10 * δ by linarith [hgeo.delta_pos]) W h)
  have h2 : z ∈ closure (thickening (10 * δ) (closure W)) := subset_closure h1
  have h4 : z ∉ closedBall (0 : ℂ) 1 := ((hgeo.buffer_W h2).2).2
  exact h4 (by rw [mem_closedBall, dist_zero_right]; exact hz.le)

/-- A function vanishing on the unit circle has zero circle average there (Cameron-Martin normalization). -/
lemma circleAverage_zero_of_sphere {f : ℂ → ℝ} (hf : ∀ z : ℂ, ‖z‖ = 1 → f z = 0) :
    Real.circleAverage f 0 1 = 0 := by
  unfold Real.circleAverage
  simp [hf]

/-- Positivity of the shifted `E₁ ∩ E₂ ∩ E₃` (note §6.4). If `A` has positive probability and `E₁`, `E₂` hold on `A`,
then for some admissible bump weight `f ∈ E3ShiftSet`, `f` is smooth, compactly supported, has zero unit-circle
average, and the shifted event `E₁ ∩ E₂ ∩ E₃` (for the metric `weylScaling D ξ f` and the measure
`μ.withDensity (exp (γ f))`) has positive probability. -/
theorem exists_E3_shift_pos {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : Ω → ℂ → ℂ → ℝ) (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) (μ : Ω → Measure ℂ)
    {ξ γ M : ℝ} (hξ : 0 < ξ) {A : Set Ω} (hAp : 0 < P A)
    (hAE : ∀ ω ∈ A, pinchFirstEventLocal (D ω) W T Q' Q δ ∧ pinchSecondEventLocal (μ ω) (D ω) U V δ M) :
    ∃ f ∈ E3ShiftSet U V W δ ξ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ Real.circleAverage f 0 1 = 0 ∧
      0 < P {ω | pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ ∧
        pinchSecondEventLocal ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))
          (fun x y => (weylScaling (D ω) ξ f x y).toReal) U V δ M ∧
        pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) V W δ} := by
  obtain ⟨c, d, hc, hd, hcdA⟩ := pinch_third_const_ae hgeo hD hAp
  obtain ⟨φ, hφC, hφc, hφ01, hφ1, hφU, hφout⟩ := S11y.exists_pinchShift_bump hgeo
  set k : ℝ := min 1 (c / (2 * d)) with hk_def
  have hk0 : 0 < k := lt_min one_pos (div_pos hc (by positivity))
  have hk1 : k ≤ 1 := min_le_left _ _
  have hkcd : k * d ≤ c / 2 := by
    have h1 : k ≤ c / (2 * d) := min_le_right _ _
    calc k * d ≤ c / (2 * d) * d := mul_le_mul_of_nonneg_right h1 hd.le
      _ = c / 2 := by field_simp
  have hfvan : ∀ z : ℂ, ‖z‖ = 1 → S11y.shiftWeight3 ξ k φ z = 0 := by
    intro z hz
    simp only [S11y.shiftWeight3, hφout z (pinch_bump_vanish_sphere hgeo hz), mul_zero]
  refine ⟨S11y.shiftWeight3 ξ k φ, ⟨k, hk0, hk1, φ, hφC, hφc, hφ01, hφ1, hφU, hφout, rfl⟩, ?_,
    S11y.shiftWeight3_hasCompactSupport hφc, circleAverage_zero_of_sphere hfvan, ?_⟩
  · show ContDiff ℝ (⊤ : ℕ∞) (fun z => ξ⁻¹ * (Real.log k * φ z))
    exact contDiff_const.mul (contDiff_const.mul hφC)
  · refine lt_of_lt_of_le hcdA (measure_mono_ae ?_)
    filter_upwards [hD] with ω hω hS
    exact S11y.pinchLocal_E3_of_shift_bump hgeo hω (γ := γ) hξ hk0 hk1 hc hkcd hφC hφc hφ01 hφ1 hφU hφout
      (hAE ω hS.1).1 (hAE ω hS.1).2 hS.2.1 hS.2.2

end S11ad
end HarmonicBalls

import HarmonicBalls.FirstPass.S11m.E1Event
import HarmonicBalls.FirstPass.S11m.SmoothBumps
import HarmonicBalls.FirstPass.S11m.WeylLengthCompact

/-!
# The first event of the shifted metric (paper `lem:E1`, on the event `F`)

The shifted metric is the Weyl scaling `weylScaling D ξ f` of a Euclidean length metric `D` by the shift weight
`f = shiftWeight ξ b bQ φQ φ0` of `SmoothBumps.lean` (`ξ f = log bQ φQ + log b φ0`). The deterministic first event
`pinchFirstEventLocal_weylScaling` (`E1Event.lean`) takes the Euclidean length property of the shifted metric as an
argument `hE`. For a continuous compactly supported weight this property is a theorem
(`weylScaling_continuous_compactSupport_length`, `WeylLengthCompact.lean`), so `hE` is discharged here. The
almost-sure form is obtained from the almost-sure Euclidean length property of `D`, inside `filter_upwards`.

Names follow Armstrong, Kuusi and Mourrat (Weyl scaling of a length metric by a bounded weight) and Berestycki-Powell
(LQG metrics as Weyl scalings of Euclidean metrics).
-/

namespace HarmonicBalls.S11m.ShiftedE1

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Deterministic first event for the Weyl-shifted metric by a continuous compactly supported weight `f`: under the
bounds `L ≥ c₁`, `A ≤ c₂`, `D(0, ∂B_{δ/2}) ≥ c₃`, `d₀ ≤ c₄` for the Euclidean length metric `D`, the metric
`weylScaling D ξ f` satisfies `E₁` (`pinchFirstEventLocal`). -/
theorem pinchFirstEventLocal_weylScaling_of_continuous {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {ξ b bQ c₁ c₂ c₃ c₄ : ℝ} (hξ : 0 < ξ) (hb1 : 1 ≤ b) (hbQ1 : 1 ≤ bQ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (hb : 2 * c₄ ≤ b * c₃) (hbQ : 2 * (b * c₂) ≤ bQ * c₁)
    (hL : c₁ ≤ pinchLocalL D Q' Q) (hA : pinchLocalA D W Q δ ≤ ENNReal.ofReal c₂)
    (hA0 : c₃ ≤ setDist D {0} (sphere (0 : ℂ) (δ / 2)))
    (hd0 : internalDiam D δ (closure (T \ thickening (3 * δ) W)) ≤ ENNReal.ofReal c₄)
    {φQ φ0 : ℂ → ℝ} (hφQ1 : ∀ z ∈ closure Q, φQ z = 1) (hφQ0 : ∀ z, z ∉ thickening δ Q → φQ z = 0)
    (hφQI : ∀ z, φQ z ∈ Icc (0 : ℝ) 1)
    (hφ01 : ∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) (hφ00 : ∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0)
    (hφ0I : ∀ z, φ0 z ∈ Icc (0 : ℝ) 1)
    {f : ℂ → ℝ} (hfsum : ∀ z, ξ * f z = Real.log bQ * φQ z + Real.log b * φ0 z)
    (hfc : Continuous f) (hfcs : HasCompactSupport f) :
    pinchFirstEventLocal (fun x y => (weylScaling D ξ f x y).toReal) W T Q' Q δ :=
  HarmonicBalls.S11m.E1Event.pinchFirstEventLocal_weylScaling hD hgeo hξ hb1 hbQ1 hc₁ hc₂ hc₃ hc₄ hb hbQ hL hA hA0
    hd0 hφQ1 hφQ0 hφQI hφ01 hφ00 hφ0I hfsum
    (HarmonicBalls.weylScaling_continuous_compactSupport_length D ξ f hD hfc hfcs).2

/-- Deterministic first event for the shifted metric `weylScaling D ξ (shiftWeight ξ b bQ φQ φ0)` (paper `lem:E1`).
The weight is smooth, compactly supported, and satisfies `ξ f = log bQ φQ + log b φ0` by `shiftWeight_props`. -/
theorem pinchFirstEventLocal_shiftWeight {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {ξ b bQ c₁ c₂ c₃ c₄ : ℝ} (hξ : 0 < ξ) (hb1 : 1 ≤ b) (hbQ1 : 1 ≤ bQ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (hb : 2 * c₄ ≤ b * c₃) (hbQ : 2 * (b * c₂) ≤ bQ * c₁)
    (hL : c₁ ≤ pinchLocalL D Q' Q) (hA : pinchLocalA D W Q δ ≤ ENNReal.ofReal c₂)
    (hA0 : c₃ ≤ setDist D {0} (sphere (0 : ℂ) (δ / 2)))
    (hd0 : internalDiam D δ (closure (T \ thickening (3 * δ) W)) ≤ ENNReal.ofReal c₄)
    {φQ φ0 : ℂ → ℝ} (hφQ : ContDiff ℝ (⊤ : ℕ∞) φQ) (hφQc : HasCompactSupport φQ)
    (hφQ1 : ∀ z ∈ closure Q, φQ z = 1) (hφQ0 : ∀ z, z ∉ thickening δ Q → φQ z = 0)
    (hφQI : ∀ z, φQ z ∈ Icc (0 : ℝ) 1)
    (hφ0 : ContDiff ℝ (⊤ : ℕ∞) φ0) (hφ0c : HasCompactSupport φ0)
    (hφ01 : ∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) (hφ00 : ∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0)
    (hφ0I : ∀ z, φ0 z ∈ Icc (0 : ℝ) 1) :
    pinchFirstEventLocal (fun x y => (weylScaling D ξ (shiftWeight ξ b bQ φQ φ0) x y).toReal) W T Q' Q δ := by
  obtain ⟨hsm, hcs, -, -, hsum⟩ := shiftWeight_props hgeo hξ hφQ hφQc hφQ0 hφ0 hφ0c hφ00
  exact pinchFirstEventLocal_weylScaling_of_continuous hD hgeo hξ hb1 hbQ1 hc₁ hc₂ hc₃ hc₄ hb hbQ hL hA hA0 hd0
    hφQ1 hφQ0 hφQI hφ01 hφ00 hφ0I hsum hsm.continuous hcs

/-- Almost surely, the first event holds for the shifted metric on the event `F` of the bounds `L ≥ c₁`,
`A ≤ c₂`, `D(0, ∂B_{δ/2}) ≥ c₃`, `d₀ ≤ c₄`. The almost-sure input is that each `D ω` is a Euclidean length metric
(the Euclidean length property of the LQG metric, used through `filter_upwards`). -/
theorem ae_pinchFirstEventLocal_shiftWeight {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (D : Ω → ℂ → ℂ → ℝ) (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {ξ b bQ c₁ c₂ c₃ c₄ : ℝ} (hξ : 0 < ξ) (hb1 : 1 ≤ b) (hbQ1 : 1 ≤ bQ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (hb : 2 * c₄ ≤ b * c₃) (hbQ : 2 * (b * c₂) ≤ bQ * c₁)
    {φQ φ0 : ℂ → ℝ} (hφQ : ContDiff ℝ (⊤ : ℕ∞) φQ) (hφQc : HasCompactSupport φQ)
    (hφQ1 : ∀ z ∈ closure Q, φQ z = 1) (hφQ0 : ∀ z, z ∉ thickening δ Q → φQ z = 0)
    (hφQI : ∀ z, φQ z ∈ Icc (0 : ℝ) 1)
    (hφ0 : ContDiff ℝ (⊤ : ℕ∞) φ0) (hφ0c : HasCompactSupport φ0)
    (hφ01 : ∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) (hφ00 : ∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0)
    (hφ0I : ∀ z, φ0 z ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, c₁ ≤ pinchLocalL (D ω) Q' Q → pinchLocalA (D ω) W Q δ ≤ ENNReal.ofReal c₂ →
      c₃ ≤ setDist (D ω) {0} (sphere (0 : ℂ) (δ / 2)) →
      internalDiam (D ω) δ (closure (T \ thickening (3 * δ) W)) ≤ ENNReal.ofReal c₄ →
      pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ (shiftWeight ξ b bQ φQ φ0) x y).toReal) W T Q' Q δ := by
  filter_upwards [hD] with ω hω hL hA hA0 hd0
  exact pinchFirstEventLocal_shiftWeight hω hgeo hξ hb1 hbQ1 hc₁ hc₂ hc₃ hc₄ hb hbQ hL hA hA0 hd0 hφQ hφQc hφQ1
    hφQ0 hφQI hφ0 hφ0c hφ01 hφ00 hφ0I

end HarmonicBalls.S11m.ShiftedE1

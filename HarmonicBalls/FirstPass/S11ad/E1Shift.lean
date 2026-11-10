import HarmonicBalls.FirstPass.S11m.FirstPos
import HarmonicBalls.FirstPass.S11m.ShiftedE1

/-!
# Shifted first event on the good box (note §6.2)

`exists_E1_shift_pos`: on the good box `F` of `exists_pinch_F_pos`, the Weyl-shifted metric by the two-bump
weight `ξ⁻¹ (log b_Q φ_Q + log b φ_0)` satisfies `E₁` almost surely, so the shifted first event has positive
probability. The weight is returned with its Cameron-Martin properties (smooth, compact support, zero unit-circle
average), which the Cameron-Martin transfer needs. Names follow Duplantier-Sheffield (Weyl scaling) and Armstrong-Kuusi-Mourrat.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HarmonicBalls
namespace S11ad

/-- §6.2 of the certificate note. For the good box of `exists_pinch_F_pos`, with `b = K := max 1 (2 (n+1)²)` and
`b_Q = K²`, the Weyl-shifted metric satisfies `E₁` almost surely on the box, hence the shifted first event has
positive probability. -/
theorem exists_E1_shift_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (D : Ω → ℂ → ℂ → ℝ) (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ b bQ : ℝ, 1 ≤ b ∧ 1 ≤ bQ ∧
      ∃ φQ φ0 : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φQ ∧ HasCompactSupport φQ ∧
        (∀ z ∈ closure Q, φQ z = 1) ∧ (∀ z, z ∉ thickening δ Q → φQ z = 0) ∧ (∀ z, φQ z ∈ Icc (0 : ℝ) 1) ∧
        ContDiff ℝ (⊤ : ℕ∞) φ0 ∧ HasCompactSupport φ0 ∧
        (∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) ∧ (∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0) ∧
        (∀ z, φ0 z ∈ Icc (0 : ℝ) 1) ∧
        ContDiff ℝ (⊤ : ℕ∞) (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) ∧
        HasCompactSupport (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) ∧
        Real.circleAverage (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) 0 1 = 0 ∧
        0 < P {ω | pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ
          (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) x y).toReal) W T Q' Q δ} := by
  obtain ⟨n, hn⟩ := HarmonicBalls.exists_pinch_F_pos hgeo hΩ D hD
  obtain ⟨φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI, hφ0, hφ0c, hφ01, hφ00, hφ0I⟩ :=
    HarmonicBalls.exists_smooth_pinch_bumps hgeo
  have hδ : 0 < δ := hgeo.delta_pos
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- the constants: c₁ = c₃ = 1/(n+1), c₂ = c₄ = n+1, b = K, b_Q = K²
  set K : ℝ := max 1 (2 * ((n : ℝ) + 1) ^ 2) with hK_def
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKk : 2 * ((n : ℝ) + 1) ^ 2 ≤ K := le_max_right _ _
  have hc₁ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hc₂ : (0 : ℝ) < (n : ℝ) + 1 := hn0
  have hb : 2 * ((n : ℝ) + 1) ≤ K * (1 / ((n : ℝ) + 1)) := by
    rw [mul_one_div, le_div_iff₀ hn0]
    nlinarith
  have hbQ : 2 * (K * ((n : ℝ) + 1)) ≤ K * K * (1 / ((n : ℝ) + 1)) := by
    rw [mul_one_div, le_div_iff₀ hn0]
    nlinarith
  have hbQ1 : 1 ≤ K * K := by nlinarith
  have hξ' : 0 < ξ := hξ
  have hae := HarmonicBalls.S11m.ShiftedE1.ae_pinchFirstEventLocal_shiftWeight D hD hgeo hξ' hK1 hbQ1
    hc₁ hc₂ hc₁ hc₂ hb hbQ hφQ hφQc hφQ1 hφQ0 hφQI hφ0 hφ0c hφ01 hφ00 hφ0I
  obtain ⟨hs1, hs2, -, hs4, -⟩ :=
    HarmonicBalls.shiftWeight_props (b := K) (bQ := K * K) hgeo hξ' hφQ hφQc hφQ0 hφ0 hφ0c hφ00
  refine ⟨K, K * K, hK1, hbQ1, φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI, hφ0, hφ0c, hφ01, hφ00, hφ0I,
    hs1, hs2, hs4, ?_⟩
  refine lt_of_lt_of_le hn (measure_mono_ae ?_)
  filter_upwards [hae] with ω hω hbox
  obtain ⟨h1, h2, h3, h4⟩ := hbox
  refine hω h1 ?_ h3 ?_
  · exact le_trans h2 (by rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (by linarith))
  · exact le_trans h4 (by rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (by linarith))

end S11ad
end HarmonicBalls

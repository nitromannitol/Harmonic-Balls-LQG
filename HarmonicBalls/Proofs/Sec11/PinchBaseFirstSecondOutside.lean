import HarmonicBalls.Proofs.Sec11.PinchOutsideFirstCertificate
import HarmonicBalls.Proofs.Sec11.PinchSecondBaseUniformOutside

/-! # Joint base-metric pinch certificates

The conditional core and positive first-certificate proofs use Leonardo
Bonanno's `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A continuity square can be selected so that its uniform dyadic diameter
tail implies simultaneous positivity of the first and second certificates. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_first_second
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (M : ℝ) :
    ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
      (∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0) ∧
      ∀ (b : ℕ → ℝ≥0∞) (p : ℝ), 2 < p → ∀ (e : ℕ → ℝ),
      Tendsto e atTop (𝓝 0) →
      (∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, b n < ENNReal.ofReal a) →
      (∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
        (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
          (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) →
      0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
        pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  obtain ⟨A, hA, hAp, hAe⟩ := h.exists_positive_outside_first_certificate hξ hgff 𝔇 h𝔇
  obtain ⟨z, L, hL, hSU, hfront, ht⟩ :=
    h.exists_square_second_base_all_outside hgrowth hγ hγ2 hξ hgff hμ hAff 𝔇 h𝔇 M
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro b p hp e he hsmall hbound
  have hpos := ht b p hp e he hsmall hbound A hA hAp
  have heq : {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} =ᵐ[P]
      {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
        pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
    filter_upwards [hAe] with ω hw
    rw [hw]
  rwa [measure_congr heq] at hpos

end HarmonicBalls

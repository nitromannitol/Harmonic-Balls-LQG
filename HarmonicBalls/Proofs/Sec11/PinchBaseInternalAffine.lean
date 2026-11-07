import HarmonicBalls.Proofs.Sec11.PinchBaseInternalClosedTail
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # Base-metric pinch positivity with proved affine invariance

The conditional smooth-shift argument uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. The closed-square tail
estimate remains an explicit hypothesis. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A continuity square can be chosen before the closed-square estimate;
that estimate implies positivity of the strengthened base-metric pinch event.
Whole-plane affine invariance is supplied by its existing proof. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_closed_tail_proved_affine
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (M : ℝ) :
    ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
      (∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0) ∧
      ∀ (c s p : ℝ), 0 < s → 2 < p → ∀ (e : ℝ → ℝ),
      Tendsto e (𝓝[>] 0) (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
        P {ω | ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
            ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
          ⨆ x ∈ complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i,
            ⨆ y ∈ complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i,
              internalMetric (𝔇 (hC ω))
                (complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i) x y} ≤
        ENNReal.ofReal ((3 * L / (2 * (2 : ℝ) ^ n)) ^
          (p + e (3 * L / (2 * (2 : ℝ) ^ n))))) →
      0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  exact h.exists_square_positive_base_internal_pinch_of_closed_tail
    hgrowth hγ hγ2 hξ hgff hμ (wholePlaneGFFAffineInvariance_proved P hC hcirc) 𝔇 h𝔇 M

#print axioms IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_closed_tail_proved_affine
end HarmonicBalls

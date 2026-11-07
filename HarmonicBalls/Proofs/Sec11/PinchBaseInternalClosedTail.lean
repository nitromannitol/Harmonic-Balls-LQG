import HarmonicBalls.Proofs.Sec11.PinchBaseFirstSecondClosedTail
import HarmonicBalls.Proofs.Sec11.PinchWholePlaneSmoothTransfer

/-! # Base-metric strengthened pinch event from closed-square tails

The conditional smooth-shift argument uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. The closed-square tail
estimate remains an explicit hypothesis. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A continuity square can be chosen before the closed-square estimate;
that estimate implies positivity of the strengthened base-metric pinch event. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_closed_tail
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
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ2 hQ
    Ω P hC hcirc μ hgff hμ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  obtain ⟨z, L, hL, hSU, hfront, hpos⟩ :=
    h.exists_square_positive_base_first_second_of_closed_tail
      hgrowth hγ hγ2 hξ hgff hμ hAff 𝔇 h𝔇 M
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro c s p hs hp e he hbound
  exact h.positive_internal_pinch_of_open_first_second hξ P M hC hcirc 𝔇 μ
    h𝔇 hgff hμ hfull ψ hψ hψint (hpos c s p hs hp e he hbound)

#print axioms IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_closed_tail
end HarmonicBalls

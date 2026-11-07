import HarmonicBalls.Proofs.Sec11.SquareDiameterMomentTail

/-! # Base-metric pinch positivity from a square-diameter moment bound

The conditional smooth-shift argument uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. The uniform moment
estimate below is a hypothesis, not an assertion about the LQG metric. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- For the selected continuity square, a uniform optimized moment estimate
implies positivity of the strengthened base-metric pinch event. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_moment
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
      ∀ (c s : ℝ), 0 < c → 0 < s → s < ξ * (lqgQ γ - 2) →
      ∀ (e : ℝ → ℝ), Tendsto e (𝓝[>] 0) (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
        let r := 3 * L / (2 * (2 : ℝ) ^ n)
        let X : Ω → ℝ≥0∞ := fun ω =>
          ⨆ x ∈ complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i,
            ⨆ y ∈ complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i,
              internalMetric (𝔇 (hC ω))
                (complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i) x y
        AEMeasurable (fun ω => (ENNReal.ofReal c)⁻¹ * X ω) P ∧
        let t := (ξ * lqgQ γ - s) / ξ ^ 2
        (∫⁻ ω, ((ENNReal.ofReal c)⁻¹ * X ω) ^ t ∂P) ≤ ENNReal.ofReal
          (r ^ (ξ * lqgQ γ * t - ξ ^ 2 * t ^ 2 / 2 + e r))) →
      0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  obtain ⟨z, L, hL, hSU, hfront, hpos⟩ :=
    h.exists_square_positive_base_internal_pinch_of_closed_tail_proved_affine
      hgrowth hγ hγ2 hξ hgff hμ 𝔇 h𝔇 M
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro c s hc hs hsh e he hm
  have hsQ : s < ξ * lqgQ γ := by nlinarith
  have hq : 2 < (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) :=
    metricDiameterTailExponent_gt_two hξ hsh
  apply hpos c s _ hs hq e he
  filter_upwards [hm] with n hn
  intro i
  have hr : 0 < 3 * L / (2 * (2 : ℝ) ^ n) := by positivity
  exact hgff.measure_scaled_power_tail_of_optimized_moment _ c _ ξ (lqgQ γ) s _
    hc hr hξ hsQ (hn i).1 (hn i).2

#print axioms IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_moment
end HarmonicBalls

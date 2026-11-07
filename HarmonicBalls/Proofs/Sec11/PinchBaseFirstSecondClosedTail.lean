import HarmonicBalls.Proofs.Sec11.PinchBaseFirstSecondOutside
import HarmonicBalls.Proofs.Sec11.DyadicClosedSquareTail

/-! # Joint base-metric pinch certificates from closed-square tails

The conditional smooth-shift argument uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. The closed-square tail
estimate remains an explicit hypothesis. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A continuity square can be chosen before the closed-square estimate;
that estimate implies joint positivity of the base-metric certificates. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_first_second_of_closed_tail
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
      0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
        pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  obtain ⟨z, L, hL, hSU, hfront, hpos⟩ :=
    h.exists_square_positive_base_first_second hgrowth hγ hγ2 hξ hgff hμ hAff 𝔇 h𝔇 M
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro c s p hs hp e he hbound
  let p' : ℝ := (2 + p) / 2
  have hp' : 2 < p' := by dsimp [p']; linarith
  have hpp : p' < p := by dsimp [p']; linarith
  obtain ⟨hsmall, htail⟩ := dyadicIntermediateInternalDiameter_thresholds_of_closed_square
    P (fun ω => 𝔇 (hC ω)) z L hL c s ξ hs hcirc p p' hp' hpp e he hbound
  exact hpos (fun n => ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s))
    p' hp' (fun _ => 0) tendsto_const_nhds hsmall htail

#print axioms IsCorrectedPinchConfiguration.exists_square_positive_base_first_second_of_closed_tail
end HarmonicBalls

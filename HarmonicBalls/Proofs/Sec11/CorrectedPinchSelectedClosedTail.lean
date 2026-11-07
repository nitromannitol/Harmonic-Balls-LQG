import HarmonicBalls.Proofs.Sec11.CorrectedPinchSelectedSquare
import HarmonicBalls.Proofs.Sec11.DyadicClosedSquareTail

/-! # Pinch positivity from a selected-square diameter estimate

The smooth-shift argument uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. The
closed-square estimate remains an explicit hypothesis. -/

namespace HarmonicBalls
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

/-- A square can be selected before applying the closed-square diameter
estimate; such an estimate then gives joint first and second positivity. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_first_second_of_closed_tail
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω) {α γ ξ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hg : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ) (hξ : 0 < ξ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (M : ℝ) (A : Set Ω)
    (hA : MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (ha : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _
      (fun ω => ENNReal.ofReal (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ)))))
    (hb : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _
      (fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6))
    : ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
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
  let : MeasurableSpace Ω := m₀
  obtain ⟨z, L, hL, hSU, hfront, hpos⟩ :=
    h.exists_square_positive_first_second_of_dyadic_existence hDG hCC hE P hC hcirc μ
      hg hμ hγ hγ₂ hα hξ 𝔇 h𝔇 M A hA hArep ha hb
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro c s p hs hp e he hbound
  let p' : ℝ := (2 + p) / 2
  have hp' : 2 < p' := by dsimp [p']; linarith
  have hpp : p' < p := by dsimp [p']; linarith
  obtain ⟨hsmall, htail⟩ := dyadicIntermediateInternalDiameter_thresholds_of_closed_square
    P (fun ω => 𝔇 (hC ω)) z L hL c s ξ hs hcirc p p' hp' hpp e he hbound
  exact hpos (fun n => ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s))
    p' hp' (fun _ => 0) tendsto_const_nhds hsmall htail

#print axioms IsCorrectedPinchConfiguration.exists_square_positive_first_second_of_closed_tail
end HarmonicBalls

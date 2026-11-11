import HarmonicBalls.Proofs.Sec11.CorrectedPinchDyadicExistence
import HarmonicBalls.Proofs.Sec11.CorrectedPinchSquareContinuity

/-! # Dyadic pinch positivity for a selected continuity square

The three LQG inputs remain subject to source review. The smooth-shift
argument uses Leonardo Bonanno's `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. -/

namespace HarmonicBalls
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

/-- A continuity square can be selected before specifying the diameter tail;
any tail of the required form then yields joint pinch positivity. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_first_second_of_dyadic_existence
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
      ∀ (b : ℕ → ℝ≥0∞) (p : ℝ), 2 < p → ∀ (e : ℕ → ℝ), Tendsto e atTop (𝓝 0) →
      (∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, b n < ENNReal.ofReal a) →
      (∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
        (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
          (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) →
      0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
        pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  obtain ⟨z, L, hL, hSU, _, _, hfront⟩ := h.exists_continuity_mass_core_square hg hμ
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro b p hp e he hsmall hbound
  exact h.positive_first_second_of_dyadic_existence hDG hCC hE P hC hcirc μ hg hμ hγ hγ₂ hα
    hξ 𝔇 h𝔇 M A hA hArep ha hb z L hL hSU hfront b p hp e he hsmall hbound

end HarmonicBalls

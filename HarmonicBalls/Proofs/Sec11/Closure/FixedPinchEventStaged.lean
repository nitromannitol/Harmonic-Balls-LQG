import HarmonicBalls.Proofs.Sec11.Closure.FixedRawPositiveOutside
import HarmonicBalls.Proofs.Sec11.Closure.PinchEventTypeZero
import HarmonicBalls.Proofs.Sec11.ClosureMeasureMeasurable

/-!
# Type-zero body of Lemma 11.12 from the staged inputs (Section 11)

Assembly of `fixed_raw_positive_null_of_staged_volume_growth_outside`
(`Closure/FixedRawPositiveOutside.lean`) into the raw canonical positivity `RawCanonicalPositiveStmt`
(`Closure/PinchEventTypeZero.lean`) of the fixed configuration, and then into the existential body of
`PinchEventPositiveProbabilityStmt` (`Draft/Section11.lean:246`) through the existing
`exists_pinchEvent_typeZero_fixed_of_raw_gff` (`ClosureMeasureMeasurable.lean`).

The hypotheses kept explicit are the staged inputs `hDG hCC hE` (`Proposed/LQG.lean`, source-checked) and the
square-tail family `hdata` (the `SquareDyadicTailInput` producer, not yet discharged). The carrier is
`Ω : Type`; the statement for `Ω : Type*` of `PinchEventPositiveProbabilityStmt` awaits the transfer lemma. Nothing is claimed beyond this conditional statement.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- Raw canonical positivity of the fixed configuration, from the staged inputs and the square-tail family. -/
theorem rawCanonicalPositiveStmt_fixed_of_staged_inputs
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hdata : ∀ (γ ξ : ℝ), 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMetric γ ξ 𝔇 →
      SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide) :
    RawCanonicalPositiveStmt fixedU fixedT fixedQ' fixedQ := by
  intro γ ξ hγ hγ₂ Ω _ P hC hcirc μ 𝔇 hgff hμ h𝔇 M _
  exact fixed_raw_positive_null_of_staged_volume_growth_outside hDG hCC hE hγ hγ₂ P 𝔇 h𝔇 hgff hμ M
    (hdata γ ξ hγ hγ₂ Ω P hC hcirc 𝔇 hgff h𝔇)

/-- The Type-zero body of Lemma 11.12 (`PinchEventPositiveProbabilityStmt`, `Draft/Section11.lean:246`) for the
fixed pinch-point configuration, from the staged inputs `hDG hCC hE` and the square-tail family `hdata`. -/
theorem exists_pinchEvent_typeZero_fixed_of_staged_inputs
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hdata : ∀ (γ ξ : ℝ), 0 < γ → γ < 2 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMetric γ ξ 𝔇 →
      SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide) :
    ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
      ∀ (γ ξ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        IsLQGMetricOfField P γ ξ 0 hC D → ∀ M : ℝ, 0 < M →
        ∃ A ⊆ {ω | pinchPointEvent (μ ω) (D ω) fixedU fixedT fixedQ' fixedQ M 1 0},
          MeasurableSet A ∧ 0 < P A :=
  exists_pinchEvent_typeZero_fixed_of_raw_gff
    (rawCanonicalPositiveStmt_fixed_of_staged_inputs hDG hCC hE hdata)


end HarmonicBalls

import HarmonicBalls.Proofs.Sec11.PinchInnerPositivity
import HarmonicBalls.Proofs.Sec11.Closure.MetricMeasurableZero
import HarmonicBalls.Proofs.Sec11.Closure.FixedGeometry

/-!
# Lemma 11.12 at zero log-charge for probability spaces in `Type` (Section 11)

The body of `PinchEventPositiveProbabilityStmt` (`HarmonicBalls/Draft/Section11.lean:246`) at `α₀ = 0`, for
probability spaces `Ω : Type`, is reduced here to one named premise: the raw positivity of the strengthened
pinch event of the canonical metric `𝔇 (hC ω)` (`RawCanonicalPositiveStmt`, the output of the conditional chain
`CorrectedPinchConditionalPositive.lean:13`). The staged input `LQGMetricFieldAxioms` is not used: the arbitrary
metric map `D` is identified with the canonical `𝔇 (hC ω)` almost surely (`Closure/MetricBridgeZero.lean`), the
canonical metric has measurable entries (`Closure/MetricMeasurableZero.lean`), and the measurable subset of the
pinch event is `exists_measurable_pos_subset_pinch` (`Proofs/Sec11/PinchInnerPositivity.lean:38`). The measurability
of the measure-valued field `μ` is the named premise `haem`. The universe restriction `Ω : Type` is open.
-/

namespace HarmonicBalls

open MeasureTheory Filter

/-- Raw positivity of the strengthened pinch event of the canonical metric, at zero log-charge, for probability
spaces in `Type`: the conclusion of the conditional chain (leftover premise, not an input). -/
def RawCanonicalPositiveStmt (U T Q' Q : Set ℂ) : Prop :=
  ∀ (γ ξ : ℝ), 0 < γ → γ < 2 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → IsLQGMetric γ ξ 𝔇 →
    ∀ M : ℝ, 0 < M →
      0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0}

/-- The body of Lemma 11.12 at `α₀ = 0` for `Ω : Type`, from the raw canonical positivity and the measurability of
the measure-valued field (leftover `haem`). -/
theorem pinchEventPositive_typeZero_of_raw {U T Q' Q : Set ℂ}
    (hconfig : IsPinchPointConfiguration U T Q' Q) (hraw : RawCanonicalPositiveStmt U T Q' Q)
    (haem : ∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsLQGMeasureOfField P γ 0 hcirc μ → AEMeasurable μ P) :
    ∀ (γ ξ : ℝ), 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      IsLQGMetricOfField P γ ξ 0 hC D → ∀ M : ℝ, 0 < M →
      ∃ A ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}, MeasurableSet A ∧ 0 < P A := by
  intro γ ξ hγ hγ' Ω _ P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨𝔇, h𝔇, hbridge⟩ := ae_metric_eq_canonical_of_isLQGMetricOfField_zero hgff hD
  have hpos := hraw γ ξ hγ hγ' Ω P hC hcirc μ 𝔇 hgff hμ h𝔇 M hM
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [ae_isEuclideanLengthMetric_of_isLQGMetricOfField_zero hgff hD, hbridge]
      with ω h1 h2
    rw [← h2]
    exact h1
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    Eventually.mono hμ (fun ω hω => hω.isLocallyFiniteMeasure)
  obtain ⟨E, hsub, hE, hEpos⟩ :=
    exists_measurable_pos_subset_pinch P hconfig M 0 (by norm_num : (0 : ℝ) < 1)
      (D := fun ω => 𝔇 (hC ω)) (fun x y => measurable_canonical_metric hgff 𝔇 h𝔇 x y)
      hmetric (haem γ Ω P hcirc μ hμ) hloc hpos
  set S : Set Ω := {ω | ¬ (D ω = 𝔇 (hC ω))} with hS
  have hS0 : P (toMeasurable P S) = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hbridge
  refine ⟨E \ toMeasurable P S, ?_, ?_, ?_⟩
  · intro ω hω
    have hωS : ω ∉ toMeasurable P S := hω.2
    have heq : D ω = 𝔇 (hC ω) := by
      by_contra hne
      exact hωS (subset_toMeasurable P S hne)
    have hpe : pinchPointEvent (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0 := (hsub hω.1).1
    show pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0
    rw [heq]
    exact hpe
  · exact hE.diff (measurableSet_toMeasurable P S)
  · rw [measure_sdiff_null hS0]
    exact hEpos

/-- The fixed pinch-point configuration (`Closure/FixedGeometry.lean`) with the Type-zero body of Lemma 11.12:
the existential witness `∃ U T Q' Q` of `PinchEventPositiveProbabilityStmt`, given the raw canonical positivity
for the fixed configuration and the measurability `haem`. -/
theorem exists_pinchEvent_typeZero_fixed_of_raw
    (hraw : RawCanonicalPositiveStmt fixedU fixedT fixedQ' fixedQ)
    (haem : ∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsLQGMeasureOfField P γ 0 hcirc μ → AEMeasurable μ P) :
    ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
      ∀ (γ ξ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        IsLQGMetricOfField P γ ξ 0 hC D → ∀ M : ℝ, 0 < M →
        ∃ A ⊆ {ω | pinchPointEvent (μ ω) (D ω) fixedU fixedT fixedQ' fixedQ M 1 0},
          MeasurableSet A ∧ 0 < P A := by
  refine ⟨fixedU, fixedT, fixedQ', fixedQ, isPinchPointConfiguration_fixed, ?_⟩
  exact pinchEventPositive_typeZero_of_raw isPinchPointConfiguration_fixed hraw haem


end HarmonicBalls

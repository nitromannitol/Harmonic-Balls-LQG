import HarmonicBalls.Proofs.Sec11.CorrectedLocalSecondPositive
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.Phase2.DerivedInputs45
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived

/-!
# Positive probability of the first two original pinch events

Lemma 11.16 of the corrected paper (`lemma:second-event-proof`): for the buffered pinch geometry,
the field `h^α = g - α log |·|` with `α < Q` and every `M > 0`, the events
`Ẽ₁` (`eq:first-event`) and `Ẽ₂(M)` (`eq:second-event`), formalized as `pinchFirstEvent` and
`pinchSecondEvent`, occur simultaneously with positive probability.

The proof follows the corrected paper: the local events `E₁` and `E₂(M)` of `s11-pinch:eq:Es`
imply `Ẽ₁` and `Ẽ₂(M)` (`pinchFirstEventLocal_subset`, `pinchSecondEventLocal_subset`; the first
inclusion uses `D ≥ 0`, which holds almost surely), and `E₁ ∩ E₂(M)` contains a measurable event of
positive probability (`pinchFirstSecondEventLocal_exists_measurable_pos`, Lemma 11.21).

## Main results

* `pinchFirstSecondEvent_exists_measurable_pos`: the measurable form at fixed data.
* `pinchSecondEventFaithfulStmt_holds`: the corrected statement `PinchSecondEventFaithfulStmt`.
* `pinchThirdEventFaithfulStmt_of_secondEvent`: Lemma 11.17 in the corrected form
  (`PinchThirdEventFaithfulStmt`), from Lemma 11.16 through
  `firstPass_11_17_corrected_derivedInputs45` and the field axioms
  `lqgMetricFieldAxiomsUnivFrozen_derived`.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set

/-- Lemma 11.16, measurable form: the intersection `Ẽ₁ ∩ Ẽ₂(M)` of the first two original pinch
events contains a measurable event of positive probability. -/
theorem pinchFirstSecondEvent_exists_measurable_pos
    {U V W T Q' Q : Set ℂ} {δ γ ξ α M : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) (hα : α < lqgQ γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M},
      MeasurableSet A ∧ 0 < P A := by
  obtain ⟨A, hA, hAm, hpos⟩ :=
    pinchFirstSecondEventLocal_exists_measurable_pos hG hγ0 hγ2 hM hα P hC hcirc μ D hGFF hμ hD
  obtain ⟨_, -, hae⟩ := hD
  set N := toMeasurable P {ω | ¬ ∀ u v, 0 ≤ D ω u v} with hN
  refine ⟨A \ N, ?_, hAm.diff (measurableSet_toMeasurable _ _), ?_⟩
  · rintro ω ⟨hωA, hωN⟩
    have hnn : ∀ u v, 0 ≤ D ω u v := by
      by_contra h
      exact hωN (subset_toMeasurable _ _ h)
    exact ⟨pinchFirstEventLocal_subset (D ω) hnn W T Q' Q δ (hA hωA).1,
      pinchSecondEventLocal_subset (μ ω) (D ω) U V δ M (hA hωA).2⟩
  · rwa [measure_sdiff_null (by
      rw [hN, measure_toMeasurable]
      exact ae_iff.mp (hae.mono fun ω h u v => (h u v).1))]

/-- Lemma 11.16, corrected form (`PinchSecondEventFaithfulStmt`): for every buffered geometry,
every `γ ∈ (0, 2)`, every `α₀ < Q` and every `M > 0`, `P[Ẽ₁ ∩ Ẽ₂(M)] > 0` (inner-measure form). -/
theorem pinchSecondEventFaithfulStmt_holds : PinchSecondEventFaithfulStmt.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ hγ₂ hα Ω _ P hC hcirc μ D hGFF hμ hD M hM
  exact pinchFirstSecondEvent_exists_measurable_pos hG hγ hγ₂ hM hα P hC hcirc μ D hGFF hμ hD

/-- Lemma 11.17, corrected form (`PinchThirdEventFaithfulStmt`), from Lemma 11.16
(`pinchSecondEventFaithfulStmt_holds`) through `firstPass_11_17_corrected_derivedInputs45`, with
the field axioms supplied by `lqgMetricFieldAxiomsUnivFrozen_derived`. -/
theorem pinchThirdEventFaithfulStmt_of_secondEvent : PinchThirdEventFaithfulStmt.{u} :=
  firstPass_11_17_corrected_derivedInputs45 pinchSecondEventFaithfulStmt_holds
    lqgMetricFieldAxiomsUnivFrozen_derived

end HarmonicBalls

import HarmonicBalls.Draft.Section11
import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import HarmonicBalls.FirstPass.S11e.CondPos
import HarmonicBalls.FirstPass.S11f.SecondThresholds
import HarmonicBalls.FirstPass.Frozen.S11f

/-!
# Section 11 second pinch event

Results of this file: Lemma 11.16 (`PinchSecondEventPositiveStmt`, paper `lemma:second-event-proof`, lines 3697-3725).

Status: OPEN. `pinchSecondEvent_of_openSteps` is a conditional theorem: it follows from the two NEW steps packaged in
`PinchSecondOpenSteps`, which are not yet proved.

* `PinchSecondOutsideStep` (the one named open point, paper lines 3697-3700): for some thresholds `c₁, c₂ > 0` the event
  `E₁ ∩ {D(∂B_δ,∂B_{2δ}) ≥ c₁} ∩ {M S ≤ c₂}` contains a set measurable for the sigma-algebra of the field outside `W`
  with positive probability. The paper asserts measurability of `E₁`, `a₁` and `S` with respect to the field outside `W`;
  the global LQG distances do not obviously have this property. Not frozen, not routed around.
* `PinchSecondMassStep` (NEW, paper lemma:massdiam conditional form, lines 3511-3523 with the conditional-equivalence
  argument after (CM-C)): the event `{μ(U) > 2c₂, diam^δ(V) ≤ c₁/2}` contains a measurable set whose conditional
  probability given the outside field is almost surely positive. Its square-diameter tail is `DDDFSquareDiameterTailFrozen`.

The deterministic threshold step is `pinchSecondEvent_of_thresholds` (`FirstPass/S11f/SecondThresholds.lean`); the
conditioning step is `measure_inter_pos_of_condExp_indicator_pos` (`FirstPass/S11e/CondPos.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- NEW, OPEN: the outside-`W` measurable threshold event of Lemma 11.16 (paper lines 3697-3725), for the configuration
`U, V, W, T, Q', Q, δ` and every LQG realization. The sigma-algebra of the field outside `W` is the comap of the
modulo-constant pairings with zero-mean tests supported away from `W`, as in `CorrectedPinchSelectedSquare`. -/
def PinchSecondOutsideStep (W T Q' Q : Set ℂ) (δ : ℝ) : Prop :=
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ 0 hcirc μ → IsLQGMetricOfField P γ ξ 0 hC D →
    MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance ≤ ‹MeasurableSpace Ω› ∧
    ∀ M : ℝ, 0 < M → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ F : Set Ω,
        MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance] F ∧
        F ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧ c₁ ≤ setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
          ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal c₂} ∧
        0 < P F

/-- NEW, OPEN: the conditional mass-diameter event of Lemma 11.16 (paper lemma:massdiam, lines 3511-3523, conditional form),
for the configuration `U, V, W, T, Q', Q, δ`. For all `c₁, c₂ > 0` there is a measurable set `H` inside
`{μ(U) > 2c₂, diam^δ(V) ≤ c₁/2}` whose conditional probability given the outside-`W` sigma-algebra is almost surely
positive. (Inner-measure form: `H` is a measurable subset of the event, as in the Draft statements.) -/
def PinchSecondMassStep (U V W : Set ℂ) (δ : ℝ) : Prop :=
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ 0 hcirc μ → IsLQGMetricOfField P γ ξ 0 hC D →
  ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
    ∃ H : Set Ω, MeasurableSet H ∧
      H ⊆ {ω | ENNReal.ofReal (2 * c₂) < μ ω U ∧ internalDiam (D ω) δ V ≤ ENNReal.ofReal (c₁ / 2)} ∧
      ∀ᵐ ω ∂P, 0 < (P[H.indicator (1 : Ω → ℝ) |
        MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance]) ω

/-- The two NEW open steps of Lemma 11.16 for one configuration (the named open point of this file). -/
def PinchSecondOpenSteps : Prop :=
  ∃ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsPinchPointProofConfiguration U V W T Q' Q δ ∧
    PinchSecondOutsideStep.{u} W T Q' Q δ ∧ PinchSecondMassStep.{u} U V W δ

/-- Lemma 11.16 (`lemma:second-event-proof`, paper line 3281), form, CONDITIONAL on `PinchSecondOpenSteps`
(OPEN). Proof: for `M > 0` take the thresholds and the outside-measurable set `F` of `PinchSecondOutsideStep`, and the
conditional mass set `H` of `PinchSecondMassStep` with the same thresholds; `P (F ∩ H) > 0` by
`measure_inter_pos_of_condExp_indicator_pos`, and `F ∩ H ⊆ Ẽ₁ ∩ Ẽ₂(M)` by `pinchSecondEvent_of_thresholds`. -/
theorem pinchSecondEvent_of_openSteps (h : PinchSecondOpenSteps.{u}) : PinchSecondEventPositiveStmt.{u} := by
  obtain ⟨U, V, W, T, Q', Q, δ, hconf, hgap, hmass⟩ := h
  refine ⟨U, V, W, T, Q', Q, δ, hconf, ?_⟩
  intro γ ξ hγ hγ₂ Ω _ P hC hcirc μ D hgff hμ hD M hM
  have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨hle, hthr⟩ := hgap γ ξ hγ hγ₂ Ω P hC hcirc μ D hgff hμ hD
  obtain ⟨c₁, c₂, hc₁, hc₂, F, hFm, hFsub, hFpos⟩ := hthr M hM
  obtain ⟨H, hHm, hHsub, hHcond⟩ := hmass γ ξ hγ hγ₂ Ω P hC hcirc μ D hgff hμ hD c₁ c₂ hc₁ hc₂
  have hpos : 0 < P (F ∩ H) :=
    measure_inter_pos_of_condExp_indicator_pos P hle hFm hHm hFpos hHcond
  refine ⟨F ∩ H, ?_, ((hle _ hFm).inter hHm), hpos⟩
  intro ω hω
  rcases hFsub hω.1 with ⟨hF1, hF2, hF3⟩
  rcases hHsub hω.2 with ⟨hH1, hH2⟩
  exact ⟨hF1, pinchSecondEvent_of_thresholds hc₁ hc₂ hH2 hF2 hF3 hH1⟩


end HarmonicBalls

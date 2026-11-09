import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11f.SecondThresholds
import HarmonicBalls.FirstPass.S11e.CondPos
import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw

/-!
# First pass, Section 11: the faithful second pinch event, Lemma 11.16 (fp-S11k, owner z3)

Target: `firstPass_11_16_corrected : PinchSecondEventFaithfulStmt` (`FirstPass/S11h/Faithful.lean:80`).

Route (corrected paper, proof of `lemma:E2`, lines 3700-3727, and `lemma:massdiam`, lines 3511-3523; ChatGPT note
`notes/fp-gaps/CHATGPT-11-15-17-faithful.md` section 5, Steps 16.1-16.3). Write `F` for the event that the first
event and the crossing and Green thresholds hold, measurable for the field outside `W`, and `H` for the mass-diameter
event of `lemma:massdiam` on the local geometry `U, V, O₁ = B_δ(V̄), W`. Then `P (F ∩ H) > 0`, since `P[1_H | outside] > 0`
almost surely (conditioning), and `F ∩ H` lies in the faithful events by the threshold inequalities.

This file proves the composition `firstPass_11_16_corrected_of_steps` from two NEW steps, which are stated here as
explicit hypotheses and are NOT yet proved: `PinchSecondExteriorStep` and `PinchSecondConditionalMassFaithfulStep`.
`firstPass_11_16_corrected` itself is not claimed (OPEN).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- NEW, OPEN: the exterior-measurable first event with the thresholds (paper `lemma:E2` proof, first sentences; ChatGPT
section 5, Step 16.2). For each buffered geometry, `γ ∈ (0, 2)`, `α₀ < Q`, `ξ`, and each LQG measure and metric of the field:
the sigma-algebra of the field outside `closure W` (the comap of the zero-mean pairings of `localModConstPairings`) is
contained in the ambient one, and for every `M > 0` there are deterministic `c₁, c₂ > 0` and an outside-measurable set `F`
of positive probability inside `Ẽ₁ ∩ {c₁ ≤ D(∂B_δ, ∂B_{2δ})} ∩ {M S ≤ c₂}`. -/
def PinchSecondExteriorStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance ≤ ‹MeasurableSpace Ω› ∧
    ∀ M : ℝ, 0 < M → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ F : Set Ω,
        MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] F ∧
        F ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧ c₁ ≤ setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
          ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal c₂} ∧
        0 < P F

/-- NEW, OPEN: the conditional mass-diameter event of `lemma:massdiam` (paper lines 3511-3523) on the local geometry
`U ⋐ V ⋐ O₁ = B_δ(V̄) ⋐ W` of a buffered configuration, with the field outside `closure W` as conditioning. For all
`c₁, c₂ > 0` there is a measurable `H` inside `{μ(U) > 2c₂, diam_D(V̄; B_δ(V̄)) < c₁/2}` whose conditional probability given
the outside sigma-algebra is almost surely positive (inner-measure form, as in `PinchSecondMassStep`). -/
def PinchSecondConditionalMassFaithfulStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
    ∃ H : Set Ω, MeasurableSet H ∧
      H ⊆ {ω | ENNReal.ofReal (2 * c₂) < μ ω U ∧ internalDiam (D ω) δ (closure V) < ENNReal.ofReal (c₁ / 2)} ∧
      ∀ᵐ ω ∂P, 0 < (P[H.indicator (1 : Ω → ℝ) |
        MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance]) ω

/-- Lemma 11.16 (`lemma:second-event-proof`, corrected), faithful form, CONDITIONAL on the two NEW steps above (OPEN).
Proof: for `M > 0` take the thresholds `c₁, c₂` and the outside-measurable `F` of `PinchSecondExteriorStep`, and the mass set
`H` of `PinchSecondConditionalMassFaithfulStep` for the same thresholds. Then `0 < P (F ∩ H)` by
`measure_inter_pos_of_condExp_indicator_pos`. On `F ∩ H`: `internalDiam V ≤ internalDiam V̄ < c₁/2 < c₁ ≤ D(∂B_δ, ∂B_{2δ})`
and `M S ≤ c₂ < 2c₂ < μ(U)`, so `pinchSecondEvent_of_thresholds` gives `Ẽ₂(M)`, and `Ẽ₁` holds from `F`. -/
theorem firstPass_11_16_corrected_of_steps (hX : PinchSecondExteriorStep.{u})
    (hM : PinchSecondConditionalMassFaithfulStep.{u}) : PinchSecondEventFaithfulStmt.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hD M hM0
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨hle, hsteps⟩ := hX U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hD
  obtain ⟨c₁, c₂, hc₁, hc₂, F, hF, hFsub, hFpos⟩ := hsteps M hM0
  obtain ⟨H, hHm, hHsub, hcond⟩ :=
    hM U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hD c₁ c₂ hc₁ hc₂
  have hpos : 0 < P (F ∩ H) :=
    measure_inter_pos_of_condExp_indicator_pos P hle hF hHm hFpos hcond
  refine ⟨F ∩ H, fun ω hω => ?_, (hle _ hF).inter hHm, hpos⟩
  obtain ⟨hE1, hsep, hS⟩ := hFsub hω.1
  obtain ⟨hmass, hdiam⟩ := hHsub hω.2
  exact ⟨hE1, pinchSecondEvent_of_thresholds hc₁ hc₂
    ((internalDiam_le_closure (D ω) δ V).trans hdiam.le) hsep hS hmass⟩

end HarmonicBalls

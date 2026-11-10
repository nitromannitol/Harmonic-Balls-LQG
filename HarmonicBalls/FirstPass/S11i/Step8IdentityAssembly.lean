import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.S11i.Step8Event
import HarmonicBalls.FirstPass.S11i.Step8ZoomFrequency

/-!
# Step 8 identification of Lemma 11.13 from its providers (fp-S11-13-hId-assembly, owner n3)

`HarmonicBalls.FirstPassS11iStep8IdentityAssembly.step8Identity_given_pinchEvent_canonical_of_phys` concludes
`Step8IdentityGivenPinchEventCanonicalStmt` (`HarmonicBalls/FirstPass/S11i/Corrected11_13.lean:109`, the OPEN binder
`hId` of `firstPass_11_13_canonical`), from the providers below and ONE named binder, `hPhys`.

`Step8IdentityCanonicalStmt γ α₀ U V W T Q' Q δ M E` unfolds to `Step8IdentityStmt γ (lqgXi γ) α₀ U V W T Q' Q δ M E`
(`Corrected11_13.lean:85`): `∃ q, (A) ∧ (B)`.

Conjunct map (A) and (B) of `Step8IdentityStmt`, with `E` the Lemma 11.12 event of the premise:
* (A) first conjunct, `q` is the same in every whole-plane model: PROVIDED by
  `HarmonicBalls.exists_localModConstField_prob` (`HarmonicBalls/FirstPass/S11i/Step8Event.lean:75`, B3). It needs
  `MeasurableSet E`, which is the first conjunct of the premise `PinchEventGammaStmt` (`S11i/Assembly13.lean:120`).
* (B) second conjunct, the zoom family `μk`, `Dk` with the window frequency converging to `q`: PROVIDED by
  `HarmonicBalls.FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency`
  (`HarmonicBalls/FirstPass/S11i/Step8ZoomFrequency.lean:103`), given the physical frequency `hPhys`.
* `hPhys`: MISSING, named binder (exact type in the theorem). For every whole-plane model at `α₀`, the window frequency of the
  unit-disc-normalized certificate event `CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) ... ((2:ℝ)^k * 2⁻¹^n) z`
  converges to `q` for `μ`-almost every centre `z ∈ B_{2^k}(0)`, for every dyadic scale `k`, with `q` the canonical
  probability of `E` (first conjunct). Its candidate inputs, none of which gives the all-scale statement on its own:
  - `HarmonicBalls.FirstPassS11iStep8Decoded.ae_unitScale_of_decoded_ball` (`S11i/Step8Decoded.lean:43`): unit-scale limit
    `P{alphaCanon ∈ F}.toReal` on `ball c₁ r₁ ⊆ ball 0 1` only, for the decoded model, under its decoder hypotheses;
  - `ae_unitScale_of_ball` (`S11i/Step8Exhaustion.lean:155`) and `unitBallFrequencyStmt_of_cover`
    (`S11i/Step8Exhaustion.lean:185`): unit scale only (`UnitBallFrequencyStmt`);
  - `unitBallFrequencyModels_at_step8Frequency` (`S11i/Step8Frequency.lean:40`): unit scale, for whole-plane models at
    `α = 0`, with the named model-level input `hPer` (pending);
  - `unitBallFrequencyModels_at_step8Frequency` and `unitBallFrequencyModels_of_inputs2` (`S11i/HzoomUnitBallDoubled.lean:143`,
    `:117`; n4, uncommitted): unit scale, from `Step8UnitBallInputs2`;
  - `ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent` (`S11ai/RootedAssembly.lean:36`, n1): the quantum bad mass in
    `ball c₁ r₁` vanishes almost surely;
  - `ae_rootedLocalIdent_assembled_kernel` (`S11r/RootedBufferKernel.lean:27`, n2): kernel clauses of the buffered family;
  - `href_discNormalized_doubledDisc_finiteKernel` (`S11i/Step8HrefBall.lean:135`): reference observations avoid the
    failure set at `q` (href), with the finite decoder kernel.
  The all-scale statement needs the unit-scale statement for the `α₀`-model, its zoom at scale `2^k`, and the identification
  of the decoded certificate event with the preimage of `E` (`hFdef` of `ae_unitScale_of_decoded_ball`). None is proved here.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8IdentityAssembly

open MeasureTheory Filter Topology Set Metric FirstPassS11i HarmonicBalls
open scoped ENNReal

/-- **Step 8 identification of Lemma 11.13 (`Step8IdentityGivenPinchEventCanonicalStmt`) from its providers.** The
Lemma 11.12 event `E` of the premise gives `MeasurableSet E`; the first conjunct of `Step8IdentityStmt` is
`exists_localModConstField_prob`; the second is `step8_zoom_family_of_ae_frequency` applied to the physical frequency
`hPhys`. The only named binder is `hPhys` (MISSING, see the module docstring). -/
theorem step8Identity_given_pinchEvent_canonical_of_phys
    (hPhys : ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
      ∀ γ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
      ∀ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E →
      ∀ q : ℝ, (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
          (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q) →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
        ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
          Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
            CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ₀) U V W T Q' Q δ₀ M
              ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    Step8IdentityGivenPinchEventCanonicalStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM hE
  obtain ⟨E, hPG⟩ := hE
  refine ⟨E, hPG, ?_⟩
  unfold Step8IdentityCanonicalStmt Step8IdentityStmt
  obtain ⟨q, hq⟩ := HarmonicBalls.exists_localModConstField_prob γ hPG.1
  refine ⟨q, fun Ω _ P hC hcirc μ D hG _ _ => hq Ω P hC hcirc hG, ?_⟩
  intro Ω _ P hC hcirc μ D hG hμ hD
  exact HarmonicBalls.FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency P U V W T Q' Q δ₀ M q μ D
    (hPhys U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM E hPG q hq Ω P hC hcirc μ D hG hμ hD)

end HarmonicBalls.FirstPassS11iStep8IdentityAssembly

#print axioms HarmonicBalls.FirstPassS11iStep8IdentityAssembly.step8Identity_given_pinchEvent_canonical_of_phys

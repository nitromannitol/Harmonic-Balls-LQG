import HarmonicBalls.FirstPass.S11i.Step8Calibration
import HarmonicBalls.FirstPass.S11i.Corrected11_13

/-!
# Step 8 calibration at the canonical exponent: the Lemma 11.12 event with its almost-sure equivalence
(fp-S11i-event-equivalence, owner n1; Codex step 2 of `notes/fp-gaps/CODEX-ASTRA-11-13-diagnosis-20261110.md`)

`pinchLocalCertificate_canonical_of_inputs` exports one Borel set `E` of pairings on `B₇(0)` that is simultaneously:

* a Lemma 11.12 event at the insertion `γ` and the canonical exponent `ξ = lqgXi γ` (`PinchEventGammaCanonicalStmt`,
  `S11i/Corrected11_13.lean:80`, i.e. `PinchEventGammaStmt`, `S11i/Assembly13.lean:120`), and
* almost surely equal to the scale-one certificate event `CertificateEvent` of the true pair `(μ, D)` at every insertion-`γ`
  model (`IsWholePlaneGFF`, `IsLQGMeasureOfField P γ γ`, `IsLQGMetricOfField P γ (lqgXi γ) γ`).

The witness is the seed witness of `pinchLocalCertificate_seed_of_inputs` (`S11i/Step8Calibration.lean`). Its equivalence is
`hall` composed with `certificateEvent_iff_pinchLocalRule`. The pinch-point inclusion follows the argument of
`firstPass_11_12_corrected_posXi_of_cert` (`S11m/Corrected11_12.lean:72`): the local pinch events imply the auxiliary events
(`pinchFirstEventLocal_subset`, `pinchSecondEventLocal_subset`, `pinchThirdEventLocal_subset`, `S11h/LocalEvents.lean`), and
`pinchPointEvent_of_auxiliary_events` (`S11e/Include.lean:30`) applies on a nonnegative length metric.

The hypotheses are exactly those of `pinchLocalCertificate_seed_of_inputs`. No new frozen input is introduced.
-/

universe u

namespace HarmonicBalls.S11i.Step8CalibrationCanonical

open MeasureTheory Set Metric Filter
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11ax HarmonicBalls.S11ay HarmonicBalls.S11m HarmonicBalls.S11m.CertificateAssembly
open HarmonicBalls.S11m.LocalRule FirstPassS11i HarmonicBalls.S11i.Step8Calibration

/-- **Lemma 11.12 at the canonical exponent with the a.s. equivalence to the certificate event.** At fixed buffered geometry,
`0 < γ < 2` and `M > 0`, there is a Borel set `E` of pairings on `B₇(0)` with `PinchEventGammaCanonicalStmt` at `γ`, such that for
every insertion-`γ` model the event `localModConstField γ ∈ E` agrees almost surely with `CertificateEvent` of `(μ, D)`. -/
theorem pinchLocalCertificate_canonical_of_inputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hBase : HarmonicBalls.S11ak.LQGMetricBaseComparisonStmt.{u})
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hFull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hOmega : insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (γ M : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0) := by
  have hξ : 0 < lqgXi γ := div_pos hγ (HarmonicBalls.lqgGraphDimension_pos γ)
  have hαQ : γ < lqgQ γ := lt_lqgQ_of_mem_Ioo hγ hγ2
  obtain ⟨E, hEm, hE⟩ := pinchLocalCertificate_seed_of_inputs hAx hLen hN2 hBase hμW hLoc hNonat hFull hgrowth hfr hmass
    hCMAbs hCMRew hComp hDsm hMf hDiam hMk hS U V W T Q' Q δ hgeo hOmega γ (lqgXi γ) hγ hγ2 hξ M hM
  have hPG : PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E := by
    unfold PinchEventGammaCanonicalStmt PinchEventGammaStmt
    refine ⟨hEm, ?_⟩
    intro Ω _ P hC hcirc μ D hgff hμ hD
    obtain ⟨hSpos, hiff⟩ := hE γ hαQ Ω P hC hcirc μ D hgff hμ hD
    refine ⟨localModConstField_measurable γ hC (ball (0 : ℂ) 7) hEm, hSpos, ?_⟩
    have hgood : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) ∧ ∀ x y, 0 ≤ D ω x y := by
      obtain ⟨𝔇, h𝔇, hDω⟩ := hD
      filter_upwards [((hAx Ω P γ (lqgXi γ) γ hC hcirc) hgff hγ hγ2 hαQ 𝔇 h𝔇).1, hDω] with ω hω hDωω
      have hEq : (fun x y => (weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun z => -γ * Real.log ‖z‖) x y).toReal) = D ω := by
        funext x y
        rw [← (hDωω x y).2, ENNReal.toReal_ofReal (hDωω x y).1]
      refine ⟨?_, fun x y => (hDωω x y).1⟩
      rw [← hEq]
      exact hω.2
    filter_upwards [hiff, hgood] with ω hω hgoodω hmem
    obtain ⟨h1, h2, h3⟩ := (certificateEvent_iff_pinchLocalRule (μ ω) (D ω) U V W T Q' Q δ M).mp (hω.mp hmem)
    exact pinchPointEvent_of_auxiliary_events (hgeo.toPinchPointProofConfiguration hgeo.U_nonempty) hgoodω.1 hgoodω.2
      (μ ω) M (pinchFirstEventLocal_subset (D ω) hgoodω.2 W T Q' Q δ h1)
      (pinchSecondEventLocal_subset (μ ω) (D ω) U V δ M h2) (pinchThirdEventLocal_subset (D ω) V W δ h3)
  refine ⟨E, hPG, ?_⟩
  intro Ω _ P hC hcirc μ D hgff hμ hD
  obtain ⟨_, hiff⟩ := hE γ hαQ Ω P hC hcirc μ D hgff hμ hD
  exact hiff

#print axioms pinchLocalCertificate_canonical_of_inputs

end HarmonicBalls.S11i.Step8CalibrationCanonical

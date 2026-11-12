import HarmonicBalls.FirstPass.Phase2.Step8AllScalesFixedMetric
import HarmonicBalls.FirstPass.Phase2.Step8SeedFixedMetric
import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos
import HarmonicBalls.FirstPass.Phase2.LengthUnivDerived
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.FirstPass.Phase2.WeylScalingCompositionDerived
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.FirstPass.Phase2.InnerMeasurableDerived
import HarmonicBalls.FirstPass.Phase2.DomainMarkovConditionalPositiveHolds
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs
import HarmonicBalls.FirstPass.Phase2.GreenPotentialHolderHolds
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.S11t
import HarmonicBalls.FirstPass.S11r
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-!
# Step 8 of Lemma 11.13: the whole-plane certificate frequency of every model

`Step8CertificateFrequencyWholePlaneStmt` (paper, Lemma 11.13, Step 8, `eq:dyadic-frequency`) for models on
`Ω : Type`. Fix a model; its metric is, almost surely, the Weyl scaling of an LQG metric `𝔇` at its field
(`IsLQGMetricOfField`). The seed of Lemma 11.12 for `𝔇` (`pinchLocalCertificate_seed_fixedMetric`) gives a measurable
coding event `E` on the field modulo constants in `B₇(0)`, which agrees almost surely with the certificate event at
radius `1` about `0` in every insertion-`γ` model of `𝔇`, and has positive probability there. An insertion-`γ` model of
`𝔇` exists on the same probability space (LQG measure at insertion `γ`; the metric is finite by the field axioms),
so `q = P[h^γ|_{B₇} ∈ E] > 0`, and `q` is the same in every whole-plane model (`localModConstField_prob_indep`).
`ae_tendsto_wholePlane_fixedMetric_of_seed` then gives the frequency `q` about `μ`-almost every point of the plane.

The other inputs of the seed are supplied by their proofs. Remaining inputs: the field axioms `hAx`, the local metric
replacement `hN2`, the continuity of the rooted metric at the insertion `hfr`, and Proposition 11.9 (`hDsm`).

## Main results
* `step8CertificateFrequencyWholePlane_of_seedInputs`: `Step8CertificateFrequencyWholePlaneStmt.{0}`.
* `firstPass_11_13_canonical_of_seedInputs`: `CorrectedLemma11_13CanonicalStmt.{0}` with the binder `hPM` replaced
  by `hN2`, `hfr` and `hDsm`; `firstPass_11_13_canonical_of_seedInputs_lemma11_10`: the same with `hDsm` replaced by
  Lemma 11.10.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open ProbabilityTheory

namespace HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed

open HarmonicBalls FirstPassS11i
open HarmonicBalls.FirstPassS11iStep8PhysExists

/-- **Step 8 of Lemma 11.13, whole-plane form, for models on `Ω : Type`.** For every buffered geometry,
`0 < γ < 2`, `α₀ < Q_γ`, `M > 0` and every whole-plane insertion-`α₀` model, there is `q > 0` such that, almost surely,
for `μ`-almost every `z ∈ ℂ`, the window frequency of the certificate events at the radii `2⁻ⁿ` about `z` tends to `q`.
Inputs: the field axioms `hAx`, the local metric replacement `hN2`, `hfr`, and Proposition 11.9 `hDsm`. -/
theorem step8CertificateFrequencyWholePlane_of_seedInputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hDsm : SmallMetricDiameterLargeMassStmt.{0}) :
    Step8CertificateFrequencyWholePlaneStmt.{0} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM Ω _ P hC hcirc μ D hG hμ hD
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hξ : 0 < lqgXi γ := isLQGMetric_xi_pos γ (lqgXi γ) 𝔇 hγ0 hγ2 h𝔇
  have hS : BundleParts.PinchSecondAnnulusStep.{0} :=
    HarmonicBalls.PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs lqgMassInnerMeasurable_derived'
      greenPotentialHolderStmt_holds
      (fun γ Ω _ P hC hcirc => lqgMeasureExistence_forall_exponents γ 0 Ω P hC hcirc)
      (fun γ Ω _ P hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc)
      (fun γ Ω _ P hC hcirc => lqgMeasureNonatomicAll_holds γ 0 Ω P hC hcirc)
      (fun γ α₀ Ω _ P hC hcirc => lqgMeasureNonatomicAll_holds γ α₀ Ω P hC hcirc)
  obtain ⟨E, hE, hseed⟩ := FirstPassPhase2Step8SeedFixedMetric.pinchLocalCertificate_seed_fixedMetric hAx
    lqgMetricLengthUniv_derived hN2
    (fun Ω _ P γ α₀ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ α₀ hC hcirc)
    LocalDecoderCommon.localLQGDecoderCommonFrozen_derived lqgMeasureNonatomicAll_holds
    lqgMeasureFullSupportStmt_holds lqgVolumeGrowthAllScalesStmt_holds
    (lqgInternalMetricWeylAeMeasurable_of_fieldAxioms hAx) MassFunctionalDerived.lqgMassFunctionalMeasurable_derived
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived S11aj.cameronMartinGFFReweighting_derived
    weylScalingCompositionFrozen_holds hDsm lqgMassInnerMeasurable_derived'
    (lqgInternalDiamInnerMeasurable_derived fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
    domainMarkovConditionalPositive_holds hS
    U V W T Q' Q δ₀ hgeom (FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeom)
    γ (lqgXi γ) hγ0 hγ2 hξ M hM 𝔇 h𝔇
  have hγQ : γ < lqgQ γ := lt_lqgQ_of_mem_Ioo hγ0 hγ2
  have : IsProbabilityMeasure P := isProbabilityMeasure_of_isWholePlaneGFF hG
  -- an insertion-`γ` model of `𝔇` on the same probability space
  obtain ⟨μγ, hμγ⟩ := lqgMeasureExistence_forall_exponents γ γ Ω P hC hcirc hG hγ0 hγ2 hγQ
  have hI := (hAx Ω P γ (lqgXi γ) γ hC hcirc hG hγ0 hγ2 hγQ 𝔇 h𝔇).1
  have hDγ : ∀ᵐ ω ∂P, ∀ u v,
      0 ≤ (weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v).toReal ∧
      ENNReal.ofReal ((weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v).toReal) =
        weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v := by
    filter_upwards [hI] with ω hω
    intro u v
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_lt (hω.1 u v))⟩
  have hpos := (hseed γ hγQ Ω P hC hcirc μγ
    (fun ω u v => (weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v).toReal)
    hG hμγ hDγ).1
  have hq : CommonProb.{0} γ E (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal := by
    intro Ω' _ P' hC' hcirc' hG'
    exact localModConstField_prob_indep hG' hG γ hE
  refine ⟨(P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal,
    ENNReal.toReal_pos hpos.ne' (measure_ne_top P _), ?_⟩
  exact FirstPassPhase2Step8AllScalesFixedMetric.ae_tendsto_wholePlane_fixedMetric_of_seed hγ0 hγ2 hα hgeom
    (hN2 γ (lqgXi γ) hγ0 hγ2 hξ) hfr hAx h𝔇 hE
    (fun Ω' _ P' hC' hcirc' μ' D' hG' hμ' hD' => (hseed γ hγQ Ω' P' hC' hcirc' μ' D' hG' hμ' hD').2) hq
    Ω P hC hcirc μ D hG hμ hDae

/-- **Lemma 11.13 (canonical exponent), with the per-model frequency proved.**
`firstPass_11_13_canonical_of_perModelFrequency` with `hPM` supplied by
`step8CertificateFrequencyWholePlane_of_seedInputs` through `step8CertificateFrequencyPerModel_of_wholePlane`.
Inputs: `hAx`, the local metric replacement `hN2`, `hfr`, and Proposition 11.9 `hDsm`. -/
theorem firstPass_11_13_canonical_of_seedInputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hDsm : SmallMetricDiameterLargeMassStmt.{0}) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13_canonical_of_perModelFrequency hAx
    (step8CertificateFrequencyPerModel_of_wholePlane
      (step8CertificateFrequencyWholePlane_of_seedInputs hAx hN2 hfr hDsm))

/-- **Lemma 11.13 (canonical exponent) from Lemma 11.10.** `firstPass_11_13_canonical_of_seedInputs` with
Proposition 11.9 supplied by its proof from the field axioms and Lemma 11.10 (`firstPass_11_9_derivedInputsFieldAxioms`).
Inputs: `hAx`, the local metric replacement `hN2`, `hfr`, and Lemma 11.10 `h1110`. -/
theorem firstPass_11_13_canonical_of_seedInputs_lemma11_10
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (h1110 : SmallMetricDiameterLargeMassSquareStmt.{0}) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13_canonical_of_seedInputs hAx hN2 hfr
    (firstPass_11_9_derivedInputsFieldAxioms (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc) h1110)

end HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed

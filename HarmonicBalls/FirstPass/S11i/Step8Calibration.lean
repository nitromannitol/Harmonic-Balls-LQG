import HarmonicBalls.FirstPass.S11m.CertificateAssembly
import HarmonicBalls.FirstPass.S11m.LocalRule
import HarmonicBalls.FirstPass.S11i.Certificate
import HarmonicBalls.FirstPass.S11h.LocalEvents

/-!
# Step 8 event calibration: the certificate seed

The Lemma 11.12 witness built by the proof of `pinchLocalCertificate_of_inputs` (`S11m/CertificateAssembly.lean:235`) is the decoded
pinch rule `decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M`. Its probability is positive
(`S11an.pinchLocal_events_pos_discharged`, `S11an.lean:212`), and it is contained almost surely in the three local pinch events
`pinchLocalRule` (`S11m/LocalRule.lean:83`). This file records two facts:

* `certificateEvent_iff_pinchLocalRule`: at Euclidean radius one and centre `0`, with `Ostar = pinchOmegaGeom W Q δ` and `η = δ`,
  the certificate event `FirstPassS11i.CertificateEvent` (`S11i/Certificate.lean:42`) is exactly the conjunction of the three local
  pinch events. This is a set identity, checked clause by clause against `S11h/LocalEvents.lean:39-51`.
* `pinchLocalCertificate_seed_of_inputs`: the witness of `pinchLocalCertificate_of_inputs`, with the almost-sure EQUIVALENCE to the
  scale-one certificate event (both directions). Its hypotheses are exactly those of
  `pinchLocalCertificate_of_inputs`.

The hypotheses are unchanged. The proof of the seed is the proof of `pinchLocalCertificate_of_inputs` with the final inclusion
replaced by `certificateEvent_iff_pinchLocalRule`.
-/

universe u

namespace HarmonicBalls.S11i.Step8Calibration

open MeasureTheory Set Metric Filter
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11ax HarmonicBalls.S11ay HarmonicBalls.S11m HarmonicBalls.S11m.CertificateAssembly
open HarmonicBalls.S11m.LocalRule FirstPassS11i

/-- Scale-one certificate identity (`Certificate.lean:42`, `LocalEvents.lean:39-51`): at radius one and centre `0`, with
`Ostar = pinchOmegaGeom W Q δ` and `η = δ`, the certificate event is the three local pinch events of `(μ, D)`. -/
theorem certificateEvent_iff_pinchLocalRule (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) :
    CertificateEvent μ D (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0 ↔
      pinchLocalRule μ D W T Q' Q U V δ M := by
  simp only [CertificateEvent, certK0, certK1, certK2, pinchLocalRule, pinchFirstEventLocal, pinchSecondEventLocal,
    pinchThirdEventLocal, pinchLocalA, pinchLocalL, rescaledSet, one_mul, mul_one, Complex.ofReal_one, add_zero,
    Set.image_id', and_assoc]

/-- The seed form of Lemma 11.12 (`PinchLocalCertificateStmt`, `S11m/Corrected11_12.lean:40`), strengthened to an equivalence: the
same Borel set `E` of pairings, with the a.s. EQUIVALENCE `E-event ↔ CertificateEvent` for the true pair `(μ, D)` at every
insertion `α < Q(γ)`. -/
def PinchLocalCertificateSeedStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, (localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
      CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)

/-- **Lemma 11.12 seed with the a.s. equivalence: the witness of `pinchLocalCertificate_of_inputs` agrees almost surely with the
scale-one certificate event.** Same inputs and same witness `E = decodedPinchRuleBall …` as `pinchLocalCertificate_of_inputs`. The
positive probability is that of the local pinch events (`pinchLocal_events_pos_discharged`). The almost-sure equivalence is `hall`
(`E ↔ pinchLocalRule`) composed with `certificateEvent_iff_pinchLocalRule` in both directions. The conclusion is
`PinchLocalCertificateSeedStmt`. -/
theorem pinchLocalCertificate_seed_of_inputs
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
    (hS : BundleParts.PinchSecondAnnulusStep.{u}) :
    PinchLocalCertificateSeedStmt.{u} := by
  intro U V W T Q' Q δ hgeo hOmega γ ξ hγ hγ2 hξ M hM
  have hΩS : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ := by
    rw [← Set.insert_eq]
    exact hOmega
  have hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ := (subset_insert _ _).trans hOmega
  by_cases hex : ∃ 𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, HarmonicBalls.IsLQGMetric γ ξ 𝔇₀
  · obtain ⟨𝔇₀, h𝔇₀⟩ := hex
    obtain ⟨Ψ, hΨm, hΨ⟩ := HarmonicBalls.S11ak.metricDecoder_punctured_ball_seven hAx γ ξ hγ hγ2 hξ
      (hN2 γ ξ hγ hγ2 hξ) 𝔇₀ h𝔇₀
    obtain ⟨Ψc, hΨc⟩ : ∃ Ψc : ModConstTestPairings (ball (0 : ℂ) 7) → ℂ → ℂ → ℝ,
        ∀ ℓ v w, Ψc ℓ v w = Ψ ℓ (v, w) := ⟨fun ℓ v w => Ψ ℓ (v, w), fun _ _ _ => rfl⟩
    have hΨcm : ∀ a b : ℂ, Measurable fun ℓ => Ψc ℓ a b := fun a b => by
      simp only [hΨc]
      exact hΨm (a, b)
    obtain ⟨Φμ, hΦμm, hΦμ⟩ := HarmonicBalls.S11m.MeasureDecoderBall.measureDecoder_ball_zero hLoc hNonat hFull
      7 (by norm_num) γ hγ hγ2
    obtain ⟨I⟩ := caExistsPinchCountSets V W T Q' Q δ
    refine ⟨decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M, ?_, ?_⟩
    · exact measurableSet_decodedPinchRuleBall I (Φ := decodedFamily Ψc)
        (fun O _ x y => measurable_decodedFamily Ψc hΨcm O x y)
        (measurable_decGreen hΦμm) (measurable_decMassU hΦμm hgeo.isOpen_U.measurableSet) M
    intro α hα Ω _ P hC hcirc μ D hgff hμ hD
    have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
    have hDm := hD
    obtain ⟨𝔇, h𝔇, hDω⟩ := hD
    have hbase := hBase γ ξ hγ hγ2 𝔇₀ 𝔇 h𝔇₀ h𝔇 Ω P hC hcirc hgff
    have hLen₀ := hLen γ ξ 𝔇₀ hγ hγ2 h𝔇₀ Ω P hC hcirc hgff
    have hAx₀ := ((hAx Ω P γ ξ α hC hcirc) hgff hγ hγ2 hα 𝔇₀ h𝔇₀).1
    have hΨω := hΨ α hα Ω P hC hcirc hgff
    have hΦμω := hΦμ α hα Ω P hC hcirc μ hgff hμ
    have hSG := ae_annulusGreenPotentialSup_ne_top_alpha hgff hγ hγ2 hα hμ hgrowth
    have hMU := ae_measure_ne_top_of_isBounded hμ U (caBoundedU hgeo)
    have hU7 : U ⊆ ball (0 : ℂ) 7 := hgeo.U_subset.trans (caAnnulusSubBall (R := 7) (by norm_num))
    have hA7 : annulus (0 : ℂ) 3 6 ⊆ ball (0 : ℂ) 7 := caAnnulusSubBall (R := 7) (by norm_num)
    have hdm := decodedMasses_ae Φμ (fun ω => localModConstField α hC (ball (0 : ℂ) 7) ω) μ
      isOpen_ball.measurableSet hU7 hA7 hΦμω
    have hgoodDw : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
        (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) ∧
        ∀ x y, 0 ≤ (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) x y := by
      filter_upwards [hAx₀] with ω hω
      exact ⟨hω.2, fun x y => ENNReal.toReal_nonneg⟩
    have hΨ' : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ v ∈ ball (0 : ℂ) 7 \ {0}, ∀ w ∈ ball (0 : ℂ) 7 \ {0},
        ENNReal.ofReal (Ψc (localModConstField α hC (ball (0 : ℂ) 7) ω) v w) =
          ENNReal.ofReal b * internalMetric
            (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
            (ball (0 : ℂ) 7 \ {0}) v w := by
      filter_upwards [hΨω] with ω hω
      obtain ⟨b, hb, h⟩ := hω
      exact ⟨b, hb, fun v hv w hw => by
        rw [hΨc]
        exact h (v, w) ⟨hv, hw⟩⟩
    have hfamω := decodedVal_ae_family Ψc (fun ω => localModConstField α hC (ball (0 : ℂ) 7) ω)
      (fun ω u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
      caIsOpenPunct caIsConnectedPunct hgoodDw hΨ'
    have hall : ∀ᵐ ω ∂P, (localModConstField α hC (ball (0 : ℂ) 7) ω ∈
        decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M ↔
        HarmonicBalls.S11m.LocalRule.pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M) := by
      filter_upwards [hbase, hLen₀, hgoodDw, hfamω, hDω, hdm, hSG, hMU] with
        ω hbω hLenω hgoodω hfω hDωω hdmω hSGω hMUω
      obtain ⟨b₁, hb₁, hb₁e⟩ := hbω
      obtain ⟨b₀, hb₀, hfamω'⟩ := hfω
      obtain ⟨c, hc0, hctop, hmUω, hmSω⟩ := hdmω
      have hD₁ : ∀ x y, D ω x y = b₁ *
          (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) x y :=
        caWeylRel hLenω hb₁ hb₁e (fun x y => ⟨(hDωω x y).1, (hDωω x y).2⟩)
      have hDlen : IsEuclideanLengthMetric (D ω) := by
        have hfun : D ω = fun x y => b₁ *
            (fun u v => (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) x y :=
          funext fun x => funext fun y => hD₁ x y
        rw [hfun]
        exact IsEuclideanLengthMetric.const_mul hgoodω.1 hb₁
      have hΦ := caDecodesOfFamily hgeo hOmega I (decodedFamily Ψc)
        (localModConstField α hC (ball (0 : ℂ) 7) ω) (Dw := fun u v =>
          (weylScaling (𝔇₀ (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) (D := D ω)
        hb₀ hb₁ hD₁ hfamω'
      have hmS : decGreen Φμ (localModConstField α hC (ball (0 : ℂ) 7) ω) =
          ENNReal.ofReal c.toReal * annulusGreenPotentialSup (μ ω) 0 3 6 := by
        have h' : decGreen Φμ (localModConstField α hC (ball (0 : ℂ) 7) ω) =
            c * annulusGreenPotentialSup (μ ω) 0 3 6 := hmSω
        rw [h', ENNReal.ofReal_toReal hctop.ne]
      have hmU : decMassU Φμ U (localModConstField α hC (ball (0 : ℂ) 7) ω) =
          ENNReal.ofReal c.toReal * μ ω U := by
        have h' : decMassU Φμ U (localModConstField α hC (ball (0 : ℂ) 7) ω) = c * μ ω U := hmUω
        rw [h', ENNReal.ofReal_toReal hctop.ne]
      have hpos' : 0 < c.toReal := ENNReal.toReal_pos hc0.ne' hctop.ne
      have hiff := HarmonicBalls.S11ax.decodedPinchRule_iff_ball hDlen (fun x y => (hDωω x y).1)
        (div_pos hb₀ hb₁) hpos' hgeo hΩ I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) (μ ω) M
        (localModConstField α hC (ball (0 : ℂ) 7) ω) hΦ hmS hmU
      constructor
      · intro hmem
        exact (hiff.mp hmem).1
      · intro hr
        exact hiff.mpr ⟨hr, hSGω, hMUω⟩
    have hsub : ∀ᵐ ω ∂P, (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ) →
        localModConstField α hC (ball (0 : ℂ) 7) ω ∈
          decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M := by
      filter_upwards [hall] with ω hω hev
      exact hω.mpr hev
    have hpos := HarmonicBalls.S11an.pinchLocal_events_pos_discharged hfr hmass hAx hCMAbs hCMRew hComp hDsm
      hMf hDiam hMk hS U V W T Q' Q δ hgeo hΩS γ α ξ hγ hγ2 hξ hα Ω P hC hcirc μ D hgff hμ hDm
      (hμW Ω P γ α hC hcirc) M hM
    refine ⟨lt_of_lt_of_le hpos (measure_mono_ae hsub), ?_⟩
    filter_upwards [hall] with ω hω
    exact hω.trans (certificateEvent_iff_pinchLocalRule (μ ω) (D ω) U V W T Q' Q δ M).symm
  · refine ⟨∅, MeasurableSet.empty, ?_⟩
    intro α _ Ω _ P hC hcirc μ D _ _ hD
    obtain ⟨𝔇, h𝔇, -⟩ := hD
    exact (hex ⟨𝔇, h𝔇⟩).elim


end HarmonicBalls.S11i.Step8Calibration

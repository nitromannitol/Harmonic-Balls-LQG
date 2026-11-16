import HarmonicBalls.FirstPass.Phase2.WeylExponentOfDG20
import HarmonicBalls.FirstPass.Phase2.ForallXiCalibrationDerived

/-!
# Step 8 identification on arbitrary sample spaces

The model-range construction transports the common event and its zoom families from sample spaces in `Type` to
sample spaces in any universe. The canonical identification and the Weyl exponent theorem give all exponents.
-/

universe u

open MeasureTheory Set Metric

namespace HarmonicBalls

open Step8PerModelUniv

/-- The same event witnessing the Step 8 identification on `Type` witnesses it in every universe. -/
theorem step8Identification_univ_of_zero (h0 : Step8IdentificationStmt.{0}) :
    Step8IdentificationStmt.{u} := by
  intro U V W T Q' Q δ hgeom γ ξ α M hγ0 hγ2 hα hM
  obtain ⟨E, ⟨hEm, hpinch⟩, q, hprob, hfreq⟩ := h0 U V W T Q' Q δ hgeom γ ξ α M hγ0 hγ2 hα hM
  refine ⟨E, ⟨hEm, ?_⟩, q, ?_, ?_⟩
  · intro Ω _ P hC hcirc μ D hG hμ hD
    have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
    have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ γ
        (fun y => y.1.circle) (fun y => y.1.measure) := by
      unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
      exact ae_modelRangeMeasure_iff.2 hμ
    obtain ⟨𝔇, h𝔇, hDae⟩ := hD
    have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ ξ γ
        (fun y => y.1.pairing) (fun y => y.1.metric) := ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
    obtain ⟨_, hpos, hae⟩ := hpinch _ _ _ _ _ _ hG' hμ' hD'
    let : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
    let : IsProbabilityMeasure (modelRangeMeasure P (modelPoint hC hcirc μ D)) :=
      FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG'
    have heq : P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} =
        modelRangeMeasure P (modelPoint hC hcirc μ D)
          {y | localModConstField γ (fun y => y.1.pairing) (ball (0 : ℂ) 7) y ∈ E} := by
      have h := S11iCert.prob_ballRestrict_alphaCanon_indep hG hG' γ E hEm
      simpa only [S11iCert.ballRestrict_alphaCanon_eq] using h
    exact ⟨localModConstField_measurable γ hC _ hEm, heq.symm ▸ hpos, ae_modelRangeMeasure_iff.1 hae⟩
  · intro Ω _ P hC hcirc μ D hG hμ hD
    have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
    have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ γ
        (fun y => y.1.circle) (fun y => y.1.measure) := by
      unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
      exact ae_modelRangeMeasure_iff.2 hμ
    obtain ⟨𝔇, h𝔇, hDae⟩ := hD
    have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ ξ γ
        (fun y => y.1.pairing) (fun y => y.1.metric) := ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
    let : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
    let : IsProbabilityMeasure (modelRangeMeasure P (modelPoint hC hcirc μ D)) :=
      FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG'
    have heq : P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} =
        modelRangeMeasure P (modelPoint hC hcirc μ D)
          {y | localModConstField γ (fun y => y.1.pairing) (ball (0 : ℂ) 7) y ∈ E} := by
      have h := S11iCert.prob_ballRestrict_alphaCanon_indep hG hG' γ E hEm
      simpa only [S11iCert.ballRestrict_alphaCanon_eq] using h
    rw [heq]
    exact hprob _ _ _ _ _ _ hG' hμ' hD'
  · intro Ω _ P hC hcirc μ D hG hμ hD
    have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
    have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ α
        (fun y => y.1.circle) (fun y => y.1.measure) := by
      unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
      exact ae_modelRangeMeasure_iff.2 hμ
    obtain ⟨𝔇, h𝔇, hDae⟩ := hD
    have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ ξ α
        (fun y => y.1.pairing) (fun y => y.1.metric) := ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
    obtain ⟨μk, Dk, hsc, hstep⟩ := hfreq _ _ _ _ _ _ hG' hμ' hD'
    refine ⟨fun k ω => μk k (toModelRange P (modelPoint hC hcirc μ D) ω),
      fun k ω => Dk k (toModelRange P (modelPoint hC hcirc μ D) ω), fun k => ?_, fun k => ?_⟩
    · exact ae_modelRangeMeasure_iff.1 (hsc k)
    · exact ae_modelRangeMeasure_iff.1 (hstep k)

/-- The Step 8 identification for every Weyl exponent and every sample-space universe. -/
theorem step8Identification_derived : Step8IdentificationStmt.{u} :=
  step8Identification_univ_of_zero
    (step8Identification_of_canonical_of_weylExponentEq
      (weylExponentEq_lqgXi_of_xiGamma xi_eq_xiGamma_derived lqgXi_eq_xiGamma_derived)
      (step8IdentificationCanonical_zero_of_decoders localMetricReplacement_zero_derived
        (lqgCanonicalDecodersMeasurableExist_of_xi_derived xi_eq_xiGamma_derived)))

end HarmonicBalls

import HarmonicBalls.FirstPass.Phase2.WeylExponentOfDG20

/-!
# Lemma 11.12 (corrected) for every insertion, with no hypothesis

`CorrectedLemma11_12Stmt` (`S11i/Faithful.lean`) is Lemma 11.12 in the corrected form `[C43]`
(corrected paper lines 3236-3244): for every buffered geometry, `γ ∈ (0, 2)`, `ξ` and `M > 0` there is
one measurable rule `E` on the local field modulo constants on `B₇(0)` such that, for every insertion
`α < Q` and every model, `E^α(M)` is measurable for `σ(h^α|_{B₇})` modulo constants, has positive
probability and is almost surely contained in the pinch-point event `Ĝ₁^{h^α}(0; M)`.

* `correctedLemma11_12_zero_derived`: the statement on sample spaces in `Type`. It is
  `closure_11_12_clean_derivedInputs37` with every input supplied by its derived theorem: the local
  metric replacement by `localMetricReplacement_zero_derived`, and the canonical decoders by the
  measurable decoders at the canonical Weyl exponent together with the identification of the Weyl
  exponent of every γ-LQG metric (`xi_eq_xiGamma_derived`).
* `correctedLemma11_12Stmt_univ_of_zero`: the rule `E` is chosen before the model, so the rule given
  on sample spaces in `Type` serves on `Ω : Type u`. The model is represented on the range of its
  sample point (`Step8PerModelUniv.ModelRange`, a type in `Type`). The measurability clause holds on
  `Ω` directly. The positive probability passes back because the range event is measurable (the
  pairings of a whole-plane GFF are measurable) and its preimage is the event on `Ω`. The almost sure
  inclusion passes back by `ae_modelRangeMeasure_iff`.
* `correctedLemma11_12_derived`: the statement at every universe.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Metric
open FirstPassS11i HarmonicBalls.FirstPassS11iStep8PhysExists

/-- **Lemma 11.12 (corrected, every insertion `α < Q`) on sample spaces in `Type`**, with no
hypothesis. -/
theorem correctedLemma11_12_zero_derived : CorrectedLemma11_12Stmt.{0} :=
  Closure.correctedLemma11_12_of_clean
    (Closure.closure_11_12_clean_derivedInputs37 lqgMetricFieldAxiomsUnivFrozen_derived
      localMetricReplacement_zero_derived
      (FirstPassS11iFinal11_13.lqgCanonicalDecodersExist_of_measurable
        (lqgCanonicalDecodersMeasurableExist_of_canonXi_derived xi_eq_xiGamma_derived
          lqgCanonicalDecodersMeasurableExistCanonXi_derived))
      wholePlaneGFFExistsFrozen_derived' wholePlaneLQGBallMassBounds_holds
      (fun Ω _ P γ hC hcirc => coordChangeAlpha0Stmt_holds γ 0 Ω P hC hcirc)
      lqgMeasureExistence_forall_field lqgInternalMetricWeylAeMeasurableFrozen_derived
      lqgMetricFieldAxioms_forall_derived domainMarkovConditionalPositive_holds greenPotentialHolderStmt_holds
      lqgMetricContinuousShiftFactI_derived dyadicCellDiamSmallFrozen_derived
      cameronMartinEventTransferFrozen_derived lqgMetricSupMeasurableFrozen_derived
      connectedSquareUnionDiamFiniteFrozen_derived)

open Step8PerModelUniv in
/-- **Lemma 11.12 (corrected) at every universe from sample spaces in `Type`.** The rule `E` of
`CorrectedLemma11_12Stmt` is chosen before the model, so the one given on sample spaces in `Type`
serves on `Ω : Type u`: the model is represented on the range of its sample point
(`Step8PerModelUniv.ModelRange`), where the whole-plane GFF, the LQG measure and the LQG metric
clauses hold. The event on the range is measurable since the pairings of the range field are
measurable, its probability is the probability of its preimage, which is the event on `Ω`, and the
almost sure inclusion on the range is an almost sure inclusion on `Ω` (`ae_modelRangeMeasure_iff`). -/
theorem correctedLemma11_12Stmt_univ_of_zero (h0 : CorrectedLemma11_12Stmt.{0}) :
    CorrectedLemma11_12Stmt.{u} := by
  intro U V W T Q' Q δ₀ hgeo hcomp γ ξ hγ0 hγ2 M hM
  obtain ⟨E, hE, hall⟩ := h0 U V W T Q' Q δ₀ hgeo hcomp γ ξ hγ0 hγ2 M hM
  refine ⟨E, hE, fun α hα Ω _ P hC hcirc μ D hG hμ hD => ?_⟩
  have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
  have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ α (fun y => y.1.circle)
      (fun y => y.1.measure) := by
    unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
    exact ae_modelRangeMeasure_iff.2 hμ
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ ξ α
      (fun y => y.1.pairing) (fun y => y.1.metric) :=
    ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
  obtain ⟨hS, hpos, hae⟩ := hall α hα (ModelRange P (modelPoint hC hcirc μ D))
    (modelRangeMeasure P (modelPoint hC hcirc μ D)) _ _ _ _ hG' hμ' hD'
  refine ⟨localModConstField_measurable α hC (ball (0 : ℂ) 7) hE, ?_, ae_modelRangeMeasure_iff.1 hae⟩
  have hSm := ((Section6.fieldSigmaAlgebraModConst_le α _ _).trans (hG'.fieldSigmaAlgebra_le α _)) _ hS
  rw [modelRangeMeasure, Measure.map_apply measurable_toModelRange hSm] at hpos
  exact hpos

/-- **Lemma 11.12 (corrected, every insertion `α < Q`, every universe)**, with no hypothesis. -/
theorem correctedLemma11_12_derived : CorrectedLemma11_12Stmt.{u} :=
  correctedLemma11_12Stmt_univ_of_zero correctedLemma11_12_zero_derived

end HarmonicBalls

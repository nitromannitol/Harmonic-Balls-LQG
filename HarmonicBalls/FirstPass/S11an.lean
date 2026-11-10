import HarmonicBalls.FirstPass.S11ad
import HarmonicBalls.FirstPass.S11ae
import HarmonicBalls.FirstPass.S11ag
import HarmonicBalls.FirstPass.S11aj
import HarmonicBalls.FirstPass.S11h.ShiftMetric11_17
import HarmonicBalls.FirstPass.S11m.WeylShift
import HarmonicBalls.FirstPass.S11m.SmoothBumps
import HarmonicBalls.FirstPass.S11y.ShiftLength
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.Proposed.LQG

/-!
# Discharge of the named hypotheses of the local event `E₁ ∩ E₂ ∩ E₃` (fp-S11an, Lemma 11.12)

Corollary `HarmonicBalls.S11an.pinchLocal_events_pos_discharged` of `HarmonicBalls.S11ad.pinchLocal_events_pos`
(FirstPass/S11ad.lean), in which all four named hypotheses are discharged:
* `hE1rule` (metric certificate of `E₁`): `S11ae.metricEventCertificate_firstLocal`;
* `hpairB` (metric-and-measure certificate of `E₁ ∩ E₂ ∩ E₃`): `pinchTriple_certificate`, the intersection of the three
  certificate sets `S11ae.metricEventCertificate_firstLocal`, `S11ag.metricMeasureEventCertificate_secondLocal` and
  `S11ae.metricEventCertificate_thirdLocal` for the same whole-plane GFF model;
* `hE1shift` (`hshift` of `metric_event_transfer_of_rule`): `hE1shift_of_frozen`, from `S11aj.metric_event_shift`, with
  the metric identity `ae_shift_metric_ofReal` (the shifted metric is the field metric of `h^ℂ + f`, from the frozen
  composition rule `WeylScalingCompositionFrozen` and `ae_weylScaling_toReal_eq_fieldMetric_shift`);
* `hE3shift` (pair shift clause): `hE3shift_of_frozen`, from `S11aj.metricMeasure_event_shift_iff`, with the measure
  shift `μ_{h+f} = e^{γf} μ_h` from the Proposed `LQGMeasureWeylScaling` (HB Fact 2.1 III, p. 9).

Named hypotheses that remain (all allowed by the task): `CameronMartinGFFMutualAbsCont` (frozen), `S11aj.CameronMartinGFFReweighting`
(named, filed for a truth check), `WeylScalingCompositionFrozen` (frozen, truth check TRUE), `LQGMeasureWeylScaling` (Proposed,
pending operator source-check) and the frozen inputs of `S11ad.pinchLocal_events_pos`.

Names follow Armstrong–Kuusi–Mourrat (internal metric, Weyl scaling) and Duplantier–Sheffield (LQG metric and measure).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

namespace HarmonicBalls
namespace S11an

/-- Universal pair certificate of the triple event `E₁ ∩ E₂ ∩ E₃` (`pinchFirstEventLocal`, `pinchSecondEventLocal`,
`pinchThirdEventLocal`), in the form of `hpairB` in `S11ad.pinchLocal_events_pos`: for every insertion `α < Q` and every
whole-plane GFF model with insertion metric `D` (`IsLQGMetricOfField`) and insertion-`α` LQG measure `μ`
(`IsLQGMeasureOfField`), there is a `distributionMeasurableSpace`-measurable set `B` such that, almost surely, the field
lies in `B` iff `E₁ ∩ E₂ ∩ E₃` holds for `(D ω, μ ω)`. Proof: intersect the three certificate sets for the same model. -/
theorem pinchTriple_certificate (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    {U V W T Q' Q : Set ℂ} {δ M γ ξ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α hC D → IsLQGMeasureOfField P γ α hcirc μ →
      ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
        ∀ᵐ ω ∂P, hC ω ∈ B ↔ (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
          pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ) := by
  intro α hα Ω _ P _ hC hcirc D μ hGFF hD hμ
  obtain ⟨B₁, hB₁m, hB₁⟩ :=
    S11ae.metricEventCertificate_firstLocal (ξ := ξ) hG hγ0 hγ2 hfr hAx α hα Ω P hC hcirc D hGFF hD
  obtain ⟨B₂, hB₂m, hB₂⟩ :=
    S11ag.metricMeasureEventCertificate_secondLocal (M := M) (ξ := ξ) hG hγ0 hγ2 hfr hmass hAx α hα Ω P hC hcirc D μ
      hGFF hD hμ
  obtain ⟨B₃, hB₃m, hB₃⟩ :=
    S11ae.metricEventCertificate_thirdLocal (ξ := ξ) V W hG.delta_pos hγ0 hγ2 hfr hAx α hα Ω P hC hcirc D hGFF hD
  refine ⟨B₁ ∩ B₂ ∩ B₃, (hB₁m.inter hB₂m).inter hB₃m, ?_⟩
  filter_upwards [hB₁, hB₂, hB₃] with ω h₁ h₂ h₃
  simp only [Set.mem_inter_iff, h₁, h₂, h₃, and_assoc]

/-- `pinchTriple_certificate` as a `MetricMeasureEventCertificateStmt` (the rule form used by `S11aj`). -/
theorem pinchTriple_stmt (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    {U V W T Q' Q : Set ℂ} {δ M γ ξ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    S11ag.MetricMeasureEventCertificateStmt.{u} γ ξ (fun d μ => pinchFirstEventLocal d W T Q' Q δ ∧
      pinchSecondEventLocal μ d U V δ M ∧ pinchThirdEventLocal d V W δ) := by
  unfold S11ag.MetricMeasureEventCertificateStmt
  exact pinchTriple_certificate hfr hmass hAx hG hγ0 hγ2

/-- A continuous compactly supported function is bounded above. -/
theorem bdd_above_of_continuous_compact {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ z, g z ≤ M := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  exact ⟨C, fun z => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z)⟩

/-- Almost surely, the Weyl-shifted metric of the pair `(D, f)` is the `ENNReal` α-metric of the shifted field `h^ℂ + f`,
with finite values. Proof: `D = e^{-ξα log}𝔇(h^ℂ)` a.s. (`IsLQGMetricOfField`), the field-level shift identity
`ae_weylScaling_toReal_eq_fieldMetric_shift`, the frozen composition `WeylScalingCompositionFrozen` for the finiteness of
`𝔇(h^ℂ + f)` (bounded `f`, `weylScaling_add_le_const_mul`). -/
theorem ae_shift_metric_ofReal (hComp : WeylScalingCompositionFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hDb : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y ∧
      ENNReal.ofReal (D ω x y) = weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) x y)
    (hξ : 0 < ξ) (f : ℂ → ℝ) (hf : Continuous f) (M : ℝ) (hM : ∀ z, f z ≤ M) :
    ∀ᵐ ω ∂P, ∀ x y, 0 ≤ (weylScaling (D ω) ξ f x y).toReal ∧
      ENNReal.ofReal ((weylScaling (D ω) ξ f x y).toReal) =
        weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) x y := by
  have hDae : ∀ᵐ ω ∂P, D ω = fieldMetric 𝔇 ξ α₀ (hC ω) := by
    filter_upwards [hDb] with ω hω
    funext x y
    show D ω x y = (weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) x y).toReal
    rw [← (hω x y).2, ENNReal.toReal_ofReal (hω x y).1]
  have hshift := ae_weylScaling_toReal_eq_fieldMetric_shift hComp hAx P γ ξ α₀ hC hcirc D hGFF hγ0 hγ2 hα 𝔇 h𝔇 hDae
    f hf
  have hcomp := hComp γ ξ α₀ Ω P hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇 f hf
  filter_upwards [hshift, hcomp, hDb] with ω h1 hc hD x y
  have hfin : weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) x y ≠ ⊤ := by
    rw [hc x y]
    have hfun : (fun z => f z - α₀ * Real.log ‖z‖) = fun z => -α₀ * Real.log ‖z‖ + f z :=
      funext fun z => by ring
    rw [hfun]
    have hle := S11m.weylScaling_add_le_const_mul (D := 𝔇 (hC ω)) hξ.le (fun z => -α₀ * Real.log ‖z‖) f M hM x y
    have hWne : weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) x y ≠ ⊤ := by
      rw [← (hD x y).2]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWne) hle
  have h3 : (weylScaling (D ω) ξ f x y).toReal =
      (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) x y).toReal :=
    congrFun (congrFun h1 x) y
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  rw [h3]
  exact ENNReal.ofReal_toReal hfin

/-- The shift clause `hE1shift` of `S11ad.pinchLocal_events_pos`, for every member of `E1ShiftSet`: the shifted first event
`E₁(D_f)` (with `D_f = e^{ξf} D` the Weyl-scaled metric) forces `h^ℂ + f ∈ B`. Proof: `S11aj.metric_event_shift` with
`Dsh = D_f`, its shifted metric identity from `ae_shift_metric_ofReal`, and the smoothness and zero circle average of the
weight `ξ⁻¹ (log bQ φQ + log b φ0)` from `HarmonicBalls.shiftWeight_props`. -/
theorem hE1shift_of_frozen {U V W T Q' Q : Set ℂ} {δ γ ξ : ℝ}
    (hCMRew : S11aj.CameronMartinGFFReweighting.{u}) (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hComp : WeylScalingCompositionFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hrule : MetricEventCertificateStmt.{u} γ ξ (fun d => pinchFirstEventLocal d W T Q' Q δ))
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (α₀ : ℝ)
    (hα : α₀ < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hDm : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ f ∈ S11ad.E1ShiftSet Q δ ξ, ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ pinchFirstEventLocal (D ω) W T Q' Q δ) →
      ∀ᵐ ω ∂P, pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ →
        addFunPairing (hC ω) f ∈ B := by
  intro f hf B hB hBiff
  obtain ⟨b, bQ, -, -, φQ, φ0, hφQ, hφQc, -, hQ0, -, hφ0, hφ0c, -, h00, -, hfeq⟩ := hf
  subst hfeq
  obtain ⟨hsm, hcs, -, hc0, -⟩ :=
    HarmonicBalls.shiftWeight_props (b := b) (bQ := bQ) hG hξ hφQ hφQc hQ0 hφ0 hφ0c h00
  obtain ⟨𝔇, h𝔇, hDb⟩ := hDm
  obtain ⟨Cb, hCb⟩ := bdd_above_of_continuous_compact hsm.continuous hcs
  have hmetricShift := ae_shift_metric_ofReal hComp hAx P γ ξ α₀ hC hcirc D hGFF hγ0 hγ2 hα 𝔇 h𝔇 hDb hξ _
    hsm.continuous Cb hCb
  exact S11aj.metric_event_shift hCMRew hCMAbs hrule P hC hcirc hGFF α₀ hα 𝔇 h𝔇 D hDb
    (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) hsm hcs hc0
    (fun ω x y => (weylScaling (D ω) ξ (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) x y).toReal) hmetricShift B hB hBiff

/-- The shift clause `hE3shift` of `S11ad.pinchLocal_events_pos`, for every member of `E3ShiftSet`: the shifted triple event
`E₁ ∩ E₂ ∩ E₃` for `(D_f, μ_f)`, with `μ_f = e^{γf} μ`, forces `h^ℂ + f ∈ B`. Proof: `S11aj.metricMeasure_event_shift_iff`;
its measure hypothesis `μ_f` from the Proposed `LQGMeasureWeylScaling` (HB Fact 2.1 III) and the identity of the circle averages
`fieldCircleAverage α₀ (addCircleAverage h f) = addCircleAverage (fieldCircleAverage α₀ h) f`; the metric hypothesis as above;
the weight has zero circle average on the unit circle by `S11ad.pinch_bump_vanish_sphere` and `S11ad.circleAverage_zero_of_sphere`. -/
theorem hE3shift_of_frozen {U V W T Q' Q : Set ℂ} {δ γ ξ : ℝ} (M : ℝ)
    (hCMRew : S11aj.CameronMartinGFFReweighting.{u}) (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hComp : WeylScalingCompositionFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hrule : S11ag.MetricMeasureEventCertificateStmt.{u} γ ξ (fun d μ => pinchFirstEventLocal d W T Q' Q δ ∧
      pinchSecondEventLocal μ d U V δ M ∧ pinchThirdEventLocal d V W δ))
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (α₀ : ℝ)
    (hα : α₀ < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hDm : IsLQGMetricOfField P γ ξ α₀ hC D) (hμW : LQGMeasureWeylScaling P γ α₀ hC hcirc) :
    ∀ f ∈ S11ad.E3ShiftSet U V W δ ξ, ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ)) →
      ∀ᵐ ω ∂P, (pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ ∧
        pinchSecondEventLocal ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))
          (fun x y => (weylScaling (D ω) ξ f x y).toReal) U V δ M ∧
        pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) V W δ) →
      addFunPairing (hC ω) f ∈ B := by
  intro f hf B hB hBiff
  obtain ⟨k, hk0, hk1, φ, hφC, hφc, hφ01, hφ1, hφU, hφout, hfeq⟩ := hf
  subst hfeq
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (S11y.shiftWeight3 ξ k φ) := by
    show ContDiff ℝ (⊤ : ℕ∞) (fun z => ξ⁻¹ * (Real.log k * φ z))
    exact contDiff_const.mul (contDiff_const.mul hφC)
  have hfc : HasCompactSupport (S11y.shiftWeight3 ξ k φ) := S11y.shiftWeight3_hasCompactSupport hφc
  have hf0 : Real.circleAverage (S11y.shiftWeight3 ξ k φ) 0 1 = 0 :=
    S11ad.circleAverage_zero_of_sphere fun z hz => by
      simp only [S11y.shiftWeight3, hφout z (S11ad.pinch_bump_vanish_sphere hG hz), mul_zero]
  obtain ⟨𝔇, h𝔇, hDb⟩ := hDm
  obtain ⟨Cb, hCb⟩ := bdd_above_of_continuous_compact hfC.continuous hfc
  have hmetricShift := ae_shift_metric_ofReal hComp hAx P γ ξ α₀ hC hcirc D hGFF hγ0 hγ2 hα 𝔇 h𝔇 hDb hξ _
    hfC.continuous Cb hCb
  have hμsh : IsLQGMeasureOfField P γ α₀ (fun ω => addCircleAverage (hcirc ω) (S11y.shiftWeight3 ξ k φ))
      (fun ω => (μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * S11y.shiftWeight3 ξ k φ x))) := by
    have hW := hμW hGFF hγ0 hγ2 hα μ hμ
    have hid : ∀ ω, fieldCircleAverage α₀ (addCircleAverage (hcirc ω) (S11y.shiftWeight3 ξ k φ)) =
        addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) (S11y.shiftWeight3 ξ k φ) := fun ω => by
      funext r z
      simp only [fieldCircleAverage, addCircleAverage]
      ring
    unfold IsLQGMeasureOfField IsLQGMeasure
    filter_upwards [hW] with ω hω
    show IsLQGLimit γ (fieldCircleAverage α₀ (addCircleAverage (hcirc ω) (S11y.shiftWeight3 ξ k φ))) _
    rw [hid ω]
    exact hω _ hfC.continuous
  have key := S11aj.metricMeasure_event_shift_iff hCMRew hCMAbs hrule P hC hcirc hGFF α₀ hα 𝔇 h𝔇 D hDb
    (S11y.shiftWeight3 ξ k φ) hfC hfc hf0
    (fun ω x y => (weylScaling (D ω) ξ (S11y.shiftWeight3 ξ k φ) x y).toReal) hmetricShift μ
    (fun ω => (μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * S11y.shiftWeight3 ξ k φ x))) hμ hμsh B hB hBiff
  filter_upwards [key] with ω hω
  exact fun hΦ => hω.mpr hΦ

/-- `S11ad.pinchLocal_events_pos` with all four named hypotheses discharged: `hE1rule` and `hpairB` by the committed
certificates (`pinchTriple_certificate`), `hE1shift` and `hE3shift` by `hE1shift_of_frozen` and `hE3shift_of_frozen`. The
conclusion is that of `S11ad.pinchLocal_events_pos`. The remaining inputs are those listed in the module docstring. -/
theorem pinchLocal_events_pos_discharged (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u}) (hCMRew : S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hOmega : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (γ α₀ ξ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hDm : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hμW : LQGMeasureWeylScaling P γ α₀ hC hcirc) (M : ℝ) (hM0 : 0 < M) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧ pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hE1 := S11ae.metricEventCertificate_firstLocal (ξ := ξ) hG hγ0 hγ2 hfr hAx
  exact S11ad.pinchLocal_events_pos hAx hCMAbs hD hM hDiam hMk hS U V W T Q' Q δ hG hOmega γ α₀ ξ hγ0 hγ2 hξ hα Ω P hC
    hcirc μ D hGFF hμ hDm M hM0 hE1
    (hE1shift_of_frozen hCMRew hCMAbs hComp hAx hE1 hG hγ0 hγ2 hξ α₀ hα P hC hcirc D hGFF hDm)
    (hE3shift_of_frozen M hCMRew hCMAbs hComp hAx (pinchTriple_stmt hfr hmass hAx (M := M) (ξ := ξ) hG hγ0 hγ2)
      hG hγ0 hγ2 hξ α₀ hα P hC hcirc D μ hGFF hμ hDm hμW)
    (pinchTriple_certificate hfr hmass hAx (M := M) (ξ := ξ) hG hγ0 hγ2 α₀ hα Ω P hC hcirc D μ hGFF hDm hμ)

end S11an
end HarmonicBalls

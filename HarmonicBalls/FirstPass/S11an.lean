import HarmonicBalls.FirstPass.S11ad
import HarmonicBalls.FirstPass.S11ae
import HarmonicBalls.FirstPass.S11ag

/-!
# Discharge of the pair certificate of the local event `E₁ ∩ E₂ ∩ E₃` (fp-S11an, Lemma 11.12)

Corollary of `HarmonicBalls.S11ad.pinchLocal_events_pos` (FirstPass/S11ad.lean). Two of its four named hypotheses are
discharged from committed results:
* `hE1rule` (metric certificate of the first local event `E₁`): `S11ae.metricEventCertificate_firstLocal`;
* `hpairB` (metric-and-measure certificate of `E₁ ∩ E₂ ∩ E₃`): `pinchTriple_certificate`, the intersection of the three
  certificate sets `S11ae.metricEventCertificate_firstLocal`, `S11ag.metricMeasureEventCertificate_secondLocal` and
  `S11ae.metricEventCertificate_thirdLocal`, each applied to the same whole-plane GFF model.

Still named hypotheses of `pinchLocal_events_pos_discharged`: the two shift clauses `hE1shift` and `hE3shift` (operator
decision R4). Their discharge through `S11aj.metric_event_shift` and `S11aj.metricMeasure_event_shift_iff` needs, besides the
measure identity `μ_{h+f} = e^{γf} μ_h`, the Weyl-scaling composition identity for the metric (`weylScaling E ξ k = weylScaling
D ξ (g + k)` when `ofReal E = weylScaling D ξ g`). No such lemma is in the repository (the `WeylLocalComposition` results are
local only), and the paper's text on it still has to be checked by the operator. See the report.

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

/-- `S11ad.pinchLocal_events_pos` with the named hypotheses `hE1rule` and `hpairB` discharged by the committed certificates
(`S11ae.metricEventCertificate_firstLocal`, `pinchTriple_certificate`). The frozen inputs `LQGInternalMetricWeylAeMeasurableFrozen`
and `LQGMassFunctionalMeasurableFrozen` (taken by those certificates) are added. The shift clauses `hE1shift` and `hE3shift`
are unchanged named hypotheses; their statements are those of `S11ad.pinchLocal_events_pos`, and the conclusion is the same. -/
theorem pinchLocal_events_pos_discharged (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hOmega : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (γ α₀ ξ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hDm : IsLQGMetricOfField P γ ξ α₀ hC D) (M : ℝ) (hM0 : 0 < M)
    (hE1shift : ∀ f ∈ S11ad.E1ShiftSet Q δ ξ, ∀ B : Set ((ℂ → ℝ) → ℝ),
      MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ pinchFirstEventLocal (D ω) W T Q' Q δ) →
      ∀ᵐ ω ∂P, pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ →
        addFunPairing (hC ω) f ∈ B)
    (hE3shift : ∀ f ∈ S11ad.E3ShiftSet U V W δ ξ, ∀ B : Set ((ℂ → ℝ) → ℝ),
      MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ) →
      ∀ᵐ ω ∂P, pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ ∧
        pinchSecondEventLocal ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))
          (fun x y => (weylScaling (D ω) ξ f x y).toReal) U V δ M ∧
        pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) V W δ →
      addFunPairing (hC ω) f ∈ B) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧ pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  exact S11ad.pinchLocal_events_pos hAx hCM hD hM hDiam hMk hS U V W T Q' Q δ hG hOmega γ α₀ ξ hγ0 hγ2 hξ hα Ω P hC
    hcirc μ D hGFF hμ hDm M hM0
    (S11ae.metricEventCertificate_firstLocal (ξ := ξ) hG hγ0 hγ2 hfr hAx) hE1shift hE3shift
    (pinchTriple_certificate hfr hmass hAx (M := M) (ξ := ξ) hG hγ0 hγ2 α₀ hα Ω P hC hcirc D μ hGFF hDm hμ)

end S11an
end HarmonicBalls

import HarmonicBalls.FirstPass.S11an
import HarmonicBalls.FirstPass.S11ay
import HarmonicBalls.FirstPass.S11bb.Stmt

/-!
# The local certificate from the decoded identification (fp-S11bb, STEP B; Lemma 11.12)

`HarmonicBalls.S11bb.pinchLocalCertificate_of_identification` proves `PinchLocalCertificateStmt`
(`FirstPass/S11m/Corrected11_12.lean:40`) from the decoded identification `PinchDecodedIdentificationStmt`
(`FirstPass/S11bb/Stmt.lean`), the positivity `HarmonicBalls.S11an.pinchLocal_events_pos_discharged`
(`FirstPass/S11an.lean:212`) and the almost sure finiteness facts `HarmonicBalls.S11ay.ae_annulusGreenPotentialSup_ne_top_alpha`
and `HarmonicBalls.S11ay.ae_measure_ne_top_of_isBounded` (`FirstPass/S11ay.lean`).

Route.
* Positivity. By the identification, `{localModConstField α h^ℂ B₇(0) ∈ E}` agrees almost surely with the local rule
  `pinchLocalRule (μ ω) (D ω) …`, because the two finiteness facts hold almost surely (`S11ay`). The local rule has
  positive probability (`S11an`), and `measure_congr` transfers this to `P{localModConstField ∈ E}`.
* Almost sure implication. On the almost sure event where `D ω` is nonnegative (`IsLQGMetricOfField`), the local rule
  gives the three non-local events of `PinchLocalCertificateStmt` by the subset lemmas `pinchFirstEventLocal_subset`,
  `pinchSecondEventLocal_subset`, `pinchThirdEventLocal_subset` (`FirstPass/S11h/LocalEvents.lean`).

`pinchPointEvent_of_local_events` (`FirstPass/S11m/LocalInclusion.lean:28`) concludes only the pinch-point event, not the
three events of `PinchLocalCertificateStmt`, so it is not the step used here.

Named inputs, all as in `S11an.pinchLocal_events_pos_discharged` except `hμW` and `hgrowth`:
`hfr`, `hmass`, `hAx`, `hCMAbs`, `hCMRew`, `hComp`, `hD`, `hM`, `hDiam`, `hMk`, `hS` (frozen or named, as there);
`hμW` in its universal form (the model `Ω` is quantified inside `PinchDecodedIdentificationStmt`, so the Proposed
`LQGMeasureWeylScaling` is needed for every `Ω`; the same form as `S11m/CertificateAssembly.lean:243`);
`hgrowth : LQGVolumeGrowthAllScalesStmt` (frozen input I2, `Draft/Section2.lean:122`, used by `S11ay`).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal
open HarmonicBalls.S11m.LocalRule

universe u

namespace HarmonicBalls
namespace S11bb

/-- **Local certificate from the decoded identification** (fp-S11bb, STEP B). For every buffered pinch geometry and
parameters `γ ∈ (0,2)`, `ξ > 0`, `M > 0`, the decoded identification `hId` gives a measurable set `E` of pairings on
`B₇(0)` with positive probability on which the three non-local events hold almost surely; this is
`PinchLocalCertificateStmt`. -/
theorem pinchLocalCertificate_of_identification
    (hId : PinchDecodedIdentificationStmt.{u})
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u})
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) :
    PinchLocalCertificateStmt.{u} := by
  intro U V W T Q' Q δ hG hOmega γ ξ hγ0 hγ2 hξ M hM0
  obtain ⟨E, hEm, hE⟩ := hId U V W T Q' Q δ hG hOmega γ ξ hγ0 hγ2 hξ M hM0
  refine ⟨E, hEm, fun α hα Ω _ P hC hcirc μ D hGFF hμ hDm => ?_⟩
  have hid := hE α hα Ω P hC hcirc μ D hGFF hμ hDm
  have hUb : Bornology.IsBounded U := by
    obtain ⟨c, ρU, ρV, ρW, hU, -, -⟩ := hG.concentric
    rw [hU]
    exact Metric.isBounded_ball
  have hfin : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ⊤ ∧ μ ω U ≠ ⊤ :=
    (S11ay.ae_annulusGreenPotentialSup_ne_top_alpha hGFF hγ0 hγ2 hα hμ hgrowth).and
      (S11ay.ae_measure_ne_top_of_isBounded hμ U hUb)
  have hA : ∀ᵐ ω ∂P, (localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
      pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M) := by
    filter_upwards [hid, hfin] with ω h1 h2
    exact ⟨fun h => (h1.1 h).1, fun h => h1.2 ⟨h, h2⟩⟩
  have hset : {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} =ᵐ[P]
      {ω | pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M} :=
    Filter.eventuallyEqSet_iff.2 hA
  have hpos : 0 < P {ω | pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M} :=
    S11an.pinchLocal_events_pos_discharged hfr hmass hAx hCMAbs hCMRew hComp hD hM hDiam hMk hS
      U V W T Q' Q δ hG hOmega γ α ξ hγ0 hγ2 hξ hα Ω P hC hcirc μ D hGFF hμ hDm (hμW Ω P γ α hC hcirc) M hM0
  refine ⟨?_, ?_⟩
  · rw [measure_congr hset]
    exact hpos
  · have hnn : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v := by
      obtain ⟨_, _, hD'⟩ := hDm
      exact hD'.mono fun ω h u v => (h u v).1
    filter_upwards [hid, hnn] with ω h1 hD0
    intro hfield
    obtain ⟨hL1, hL2, hL3⟩ := (h1.1 hfield).1
    exact ⟨pinchFirstEventLocal_subset (D ω) hD0 W T Q' Q δ hL1,
      pinchSecondEventLocal_subset (μ ω) (D ω) U V δ M hL2,
      pinchThirdEventLocal_subset (D ω) V W δ hL3⟩

end S11bb
end HarmonicBalls

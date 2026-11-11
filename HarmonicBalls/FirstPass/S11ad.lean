import HarmonicBalls.FirstPass.S11ad.E12
import HarmonicBalls.FirstPass.S11ad.Shift3

/-!
# Positivity of the bounded certificate of Lemma 11.12 (route of note §6.2–6.4)

Main result: `HarmonicBalls.S11ad.pinchLocal_events_pos`, the positivity of
the local event `E₁ ∩ E₂ ∩ E₃` (`pinchFirstEventLocal`, `pinchSecondEventLocal`, `pinchThirdEventLocal`) for the
whole-plane GFF `hC`, the LQG measure `μ` and the LQG metric `D`.

Route:
* `S11ad/E1Shift`: the Weyl-shifted first event has positive probability on the good box.
* `S11ad/ExteriorA`, `S11ad/ExteriorE1`: outside-`W` versions of `E₁`, so the local second event applies.
* `S11ad/E12`: Cameron–Martin transfer of `E₁` to the base field, then `E₂` on the outside version.
* `S11ad/Third`, `S11ad/Shift3`: choice of `c, d`, the bump shift `u = ξ⁻¹ log k φ` and `E₃` after shifting.
* This file: the final Cameron–Martin transfer of the whole event `E₁ ∩ E₂ ∩ E₃` (`cm_predicate_transfer`).

Named inputs (not proved here; see the hypotheses of `pinchLocal_events_pos`):
* `hCM` (`CameronMartinGFFMutualAbsCont`), and the literature/locality inputs of `S11y.pinchLocal_E2_positive`
  (`hAx`, `hD`, `hM`, `hDiam`, `hMk`, `hS`).
* `hE1rule`: `MetricEventCertificateStmt` for `E₁` (rule measurability (e) of `E₁`, discharged in FirstPass/S11ae).
* `hE1shift`, `hE3shift`: the shift clauses of the Cameron–Martin transfers (pending).
* `hpairB`: the distribution-measurable certificate of the pair event `E₁ ∩ E₂ ∩ E₃` for the field `hC`, the metric `D`
  and the measure `μ` (pending: no rule for pair events exists yet).

Names follow Armstrong–Kuusi–Mourrat (internal metric, Weyl scaling) and Duplantier–Sheffield (LQG metric and measure).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

namespace HarmonicBalls
namespace S11ad

/-- Positivity of the bounded certificate of Lemma 11.12 (paper `lem:11.12`, corrected draft; route §6.2–6.4). The event
`E₁ ∩ E₂ ∩ E₃` has positive probability. `M > 0` is not needed by the argument (the event is defined for every `M`). -/
theorem pinchLocal_events_pos (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hOmega : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (γ α₀ ξ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hDm : IsLQGMetricOfField P γ ξ α₀ hC D) (M : ℝ) (_hM0 : 0 < M)
    (hE1rule : MetricEventCertificateStmt.{u} γ ξ (fun E => pinchFirstEventLocal E W T Q' Q δ))
    (hE1shift : ∀ f ∈ E1ShiftSet Q δ ξ, ∀ B : Set ((ℂ → ℝ) → ℝ),
      MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ pinchFirstEventLocal (D ω) W T Q' Q δ) →
      ∀ᵐ ω ∂P, pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ →
        addFunPairing (hC ω) f ∈ B)
    (hE3shift : ∀ f ∈ E3ShiftSet U V W δ ξ, ∀ B : Set ((ℂ → ℝ) → ℝ),
      MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ) →
      ∀ᵐ ω ∂P, pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ ∧
        pinchSecondEventLocal ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x)))
          (fun x y => (weylScaling (D ω) ξ f x y).toReal) U V δ M ∧
        pinchThirdEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) V W δ →
      addFunPairing (hC ω) f ∈ B)
    (hpairB : ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
      ∀ᵐ ω ∂P, hC ω ∈ B ↔ (pinchFirstEventLocal (D ω) W T Q' Q δ ∧
        pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧ pinchThirdEventLocal (D ω) V W δ)) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧ pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    (metric_locality_of_frozen hAx γ ξ α₀ hγ0 hγ2 hα Ω P hC hcirc D hGFF hDm).1
  -- (1) `E₁ ∩ E₂` on a measurable set of positive probability (§6.2–6.3)
  obtain ⟨A2, hA2m, hA2p, hA2E⟩ :=
    pinchLocal_E12_pos hAx hCM hD hM hDiam hMk hS U V W T Q' Q δ hG hOmega γ α₀ ξ hγ0 hγ2 hξ hα Ω P hC hcirc μ D
      hGFF hμ hDm M hE1rule hE1shift
  -- (2) the bump shift for `E₃` keeps `E₁ ∩ E₂` and gives `E₃` (§6.4)
  obtain ⟨f, hf, hfC, hfc, hf0, hposS⟩ :=
    exists_E3_shift_pos (γ := γ) hG D hmetric μ hξ hA2p hA2E
  -- (3) Cameron–Martin transfer of the whole event to the base field
  obtain ⟨B, hB, hiff⟩ := hpairB
  obtain ⟨A, hAsub, hAm, hAp⟩ :=
    cm_predicate_transfer hCM P hC hcirc hGFF f hfC hfc hf0
      (fun p : (ℂ → ℂ → ℝ) × Measure ℂ => pinchFirstEventLocal p.1 W T Q' Q δ ∧
        pinchSecondEventLocal p.2 p.1 U V δ M ∧ pinchThirdEventLocal p.1 V W δ)
      (fun ω => (D ω, μ ω))
      (fun ω => (fun x y => (weylScaling (D ω) ξ f x y).toReal,
        (μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))))
      B hB (hiff.mono fun _ h => h.mp) (hE3shift f hf B hB hiff) hposS
  exact lt_of_lt_of_le hAp (measure_mono hAsub)

end S11ad
end HarmonicBalls

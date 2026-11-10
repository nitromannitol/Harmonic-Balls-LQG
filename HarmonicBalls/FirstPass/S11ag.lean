import HarmonicBalls.FirstPass.S11ab
import HarmonicBalls.FirstPass.S11ag.Metric
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.GreenField11_17
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11h.MassCoord11_17
import HarmonicBalls.FirstPass.S11j.FieldLevel11_15
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Frozen.S11j

/-! # Metric-and-measure event certificate for the second local event (fp-S11ag)

The pair version of `MetricEventCertificateStmt` (`FirstPass/S11ab.lean`): the event is a predicate `Φ` of the metric `D`
and of the insertion-`α` LQG measure `μ` of the same whole-plane GFF. It is the form that the Cameron-Martin transfer of the
second local event `E₂ = {a₁ > d₁, μ(U) > M S}` (`pinchSecondEventLocal`, `FirstPass/S11h/LocalEvents.lean`) needs (z3,
blocker B2). The statement is a named form that the decoded rule must supply; it is not an External or Proposed input.
-/

namespace HarmonicBalls.S11ag

open MeasureTheory Set Metric

universe u

/-- Named form, pair (metric and measure) version of the decoded rule: for every insertion `α < Q` and every whole-plane
GFF model with insertion metric `D` (`IsLQGMetricOfField`) and insertion-`α` LQG measure `μ` (`IsLQGMeasureOfField`), there is
a `distributionMeasurableSpace`-measurable set `B` of distributions such that, almost surely, the field lies in `B` iff the
pair `(D ω, μ ω)` satisfies `Φ`. Not an External or Proposed Prop; a form the rule must supply. -/
def MetricMeasureEventCertificateStmt (γ ξ : ℝ) (Φ : (ℂ → ℂ → ℝ) → Measure ℂ → Prop) : Prop :=
  ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α hC D → IsLQGMeasureOfField P γ α hcirc μ →
    ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
      ∀ᵐ ω ∂P, hC ω ∈ B ↔ Φ (D ω) (μ ω)

/-- The second local event `E₂ = {a₁ > d₁, μ(U) > M S}` (`pinchSecondEventLocal`, `FirstPass/S11h/LocalEvents.lean`)
satisfies the pair certificate for `0 < γ < 2`, from the buffered geometry (`IsBufferedPinchGeometry`, for the open set `U`
and `0 < δ`) and the frozen inputs `LQGInternalMetricWeylAeMeasurableFrozen`, `LQGMassFunctionalMeasurableFrozen` and
`LQGMetricFieldAxiomsUnivFrozen`. The metric clause is `metricSecond_certificate`. The mass clause `M S < μ(U)` with
`S = annulusGreenPotentialSup μ 0 3 6` is a field-level event: `exists_mass_open_functional` gives the mass of the open set
`U`, and `exists_annulusGreenField` gives the annular Green supremum `S`, both as `distributionMeasurableSpace`-measurable
functionals of the field. The frozen input `LQGMassInnerMeasurableFrozen` is not used. The shifted clause (`hshift`) is not
part of this statement. -/
theorem metricMeasureEventCertificate_secondLocal {U V W T Q' Q : Set ℂ} {δ M γ ξ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hax : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    MetricMeasureEventCertificateStmt.{u} γ ξ (fun d μ => pinchSecondEventLocal μ d U V δ M) := by
  unfold MetricMeasureEventCertificateStmt
  intro α hα Ω _ P _ hC hcirc D μ hGFF hD hμ
  obtain ⟨B₁, hB₁m, hB₁⟩ :=
    metricSecond_certificate V hgeo.delta_pos hγ hγ₂ hfr hax α hα P hC hcirc D hGFF hD
  obtain ⟨F, hFm, hF⟩ :=
    exists_mass_open_functional hmass P hC hcirc μ hGFF γ α hγ hγ₂ hα hμ U hgeo.isOpen_U
  obtain ⟨G, hGm, hG, -⟩ :=
    exists_annulusGreenField hmass P hC hcirc μ hGFF γ α hγ hγ₂ hα hμ 0 3 6 (fun _ => 0)
      continuous_const (fun _ _ => rfl)
  have hF' : ∀ᵐ ω ∂P, F (hC ω) = μ ω U := by
    filter_upwards [hF (fun _ => 0) continuous_const (fun _ _ => rfl)] with ω hω
    rwa [addFunPairing_zero_shift] at hω
  refine ⟨B₁ ∩ {h | ENNReal.ofReal M * G h < F h}, hB₁m.inter (measurableSet_lt (hGm.const_mul _) hFm), ?_⟩
  filter_upwards [hB₁, hF', hG] with ω h₁ h₂ h₃
  simp only [pinchSecondEventLocal, Set.mem_inter_iff, Set.mem_ofPred_eq, h₁, h₂, h₃]

end HarmonicBalls.S11ag

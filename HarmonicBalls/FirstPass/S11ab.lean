import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Draft.Section11
import HarmonicBalls.FirstPass.S11j.CertificateTransfer

/-!
# Cameron-Martin transfer of the first pinch event (fp-S11ab, owner z7)

Item (c) of z4's `PinchLocalCertificateStmt` remainder (reports/z4.md): from `P(E1 of the shifted metric) > 0` to
`P(E1 of D) > 0`, where `E1` is `pinchFirstEvent` (Draft/Section11.lean, eq:first-event) and the shift is a smooth
compactly supported `f` with zero unit-circle average (route notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md,
section 6.2, last sentence).

Proved here, from the frozen `CameronMartinGFFMutualAbsCont` (FirstPass/Frozen/S11d.lean) through
`cameronMartinFieldCertificateTransfer` (FirstPass/S11j/CertificateTransfer.lean):
* `cm_pinchFirstEvent_transfer`: a common distribution-measurable field certificate for the two events gives a
  measurable subset of the first event of `D` of positive probability whenever the shifted first event has positive
  probability.
* `firstEventFieldCertificate_of_measurable`: the certificate for `E1(D)` and `E1(D_{h+f})` is equivalent to the
  distribution-measurability of the first-event predicate of the insertion metric, `FirstEventMeasurable`.
* `cm_pinchFirstEvent_pos_of_shift`: the two combined, conditional on `FirstEventMeasurable`.

OPEN (not proved, not an input): `FirstEventMeasurable` (z4's Q3). Nothing in the repository gives the
distribution-measurability of `T ↦ weylScaling (𝔇 T) ξ (-α log‖·‖) u v` for `α ≠ 0`: `IsLQGMetric.measurable_apply`
covers only the unweighted metric `𝔇 T z w`, and the weighted metric is an infimum over length-parametrized paths.
The certificate is therefore a hypothesis of the conditional theorems below; it is not a literature input and has
no `External`/`Proposed` Prop.

Terminology: Duplantier-Sheffield, Berestycki-Powell (LQG measures and metrics), Gwynne-Miller 2021 (metric
`𝔇` and Weyl scaling), Armitage-Gardiner (potential theory); Miller-Sheffield arXiv:1302.4738v2 Prop. 2.9
(Cameron-Martin equivalence, behind the frozen input).
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- The real-valued metric of the insertion field `T - α log|·|` built from a distribution `T`: the Weyl scaling of
`𝔇 T` with weight `-α log|·|`, the convention of `IsLQGMetricOfField` (Weyl scaling `D_{h - α log|·|}`, GM21
Remark 1.5), read as a real function. -/
noncomputable def insertionMetricOf (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α : ℝ) (T : (ℂ → ℝ) → ℝ) :
    ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 T) ξ (fun x => -α * Real.log ‖x‖) u v).toReal

/-- Field-level certificate for the pair of events `E0`, `Ef` under the shift `f` of a whole-plane GFF `hC`: one
distribution-measurable event `B` with `ω ∈ E0 ↔ hC ω ∈ B` and `ω ∈ Ef ↔ addFunPairing (hC ω) f ∈ B` almost
surely. This is exactly the hypothesis of `cameronMartinFieldCertificateTransfer`. -/
def FirstEventFieldCertificate {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (f : ℂ → ℝ) (E0 Ef : Set Ω) : Prop :=
  ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
    (∀ᵐ ω ∂P, ω ∈ E0 ↔ hC ω ∈ B) ∧ (∀ᵐ ω ∂P, ω ∈ Ef ↔ addFunPairing (hC ω) f ∈ B)

/-- OPEN, z4's Q3 (not proved; not an input). The first pinch event `pinchFirstEvent` of the insertion metric
`insertionMetricOf 𝔇 ξ α T` is a distribution-measurable predicate of the distribution `T`. -/
def FirstEventMeasurable (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α : ℝ) (W Tset Q' Q : Set ℂ) (δ : ℝ) : Prop :=
  MeasurableSet[distributionMeasurableSpace]
    {T : (ℂ → ℝ) → ℝ | pinchFirstEvent (insertionMetricOf 𝔇 ξ α T) W Tset Q' Q δ}

/-- Cameron-Martin transfer of the first pinch event, from a field certificate. If `Ef` (the first event of the
shifted field) has positive probability, then some measurable subset of `E0` (the first event of `D`) has positive
probability. Proof: `cameronMartinFieldCertificateTransfer` with the frozen `CameronMartinGFFMutualAbsCont`. -/
theorem cm_pinchFirstEvent_transfer (hCM : CameronMartinGFFMutualAbsCont.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (f : ℂ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hf0 : Real.circleAverage f 0 1 = 0) (E0 Ef : Set Ω) (hcert : FirstEventFieldCertificate P hC f E0 Ef) :
    0 < P Ef → ∃ A ⊆ E0, MeasurableSet A ∧ 0 < P A := by
  obtain ⟨B, hB, hE0, hEf⟩ := hcert
  exact (cameronMartinFieldCertificateTransfer hCM Ω P hC hcirc f hGFF hf hfc hf0 E0 Ef ⟨B, hB, hE0, hEf⟩).2.2.2

/-- The first pinch event of the metric `D` of an insertion LQG field `hC - α log|·|` (`IsLQGMetricOfField`), and of
the shifted field `hC + f`, has a field certificate as soon as `FirstEventMeasurable` holds: the metric `D` agrees
almost surely with `insertionMetricOf 𝔇 ξ α (hC ω)`, which is what `hD` records (the real parts of the Weyl scaling;
`ENNReal.toReal_ofReal` for `0 ≤ D`). -/
theorem firstEventFieldCertificate_of_measurable (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α : ℝ) (W Tset Q' Q : Set ℂ)
    (δ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (f : ℂ → ℝ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmeas : FirstEventMeasurable 𝔇 ξ α W Tset Q' Q δ) :
    FirstEventFieldCertificate P hC f {ω | pinchFirstEvent (D ω) W Tset Q' Q δ}
      {ω | pinchFirstEvent (insertionMetricOf 𝔇 ξ α (addFunPairing (hC ω) f)) W Tset Q' Q δ} := by
  refine ⟨{T | pinchFirstEvent (insertionMetricOf 𝔇 ξ α T) W Tset Q' Q δ}, hmeas, ?_,
    Filter.Eventually.of_forall fun ω => Iff.rfl⟩
  filter_upwards [hD] with ω hω
  have hfun : D ω = insertionMetricOf 𝔇 ξ α (hC ω) := by
    funext u v
    show D ω u v = (weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v).toReal
    rw [← (hω u v).2, ENNReal.toReal_ofReal (hω u v).1]
  show pinchFirstEvent (D ω) W Tset Q' Q δ ↔ pinchFirstEvent (insertionMetricOf 𝔇 ξ α (hC ω)) W Tset Q' Q δ
  rw [hfun]

/-- Cameron-Martin transfer of the first pinch event (z4 item (c)), conditional on the open input `FirstEventMeasurable`
(Q3). If the first event of the shifted metric `D_{hC+f}` has positive probability, then the first event of `D` has
positive probability, witnessed by a measurable subset. -/
theorem cm_pinchFirstEvent_pos_of_shift (hCM : CameronMartinGFFMutualAbsCont.{u}) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α : ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (W Tset Q' Q : Set ℂ) (δ : ℝ) (hmeas : FirstEventMeasurable 𝔇 ξ α W Tset Q' Q δ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (hf0 : Real.circleAverage f 0 1 = 0)
    (hshift : 0 < P {ω | pinchFirstEvent (insertionMetricOf 𝔇 ξ α (addFunPairing (hC ω) f)) W Tset Q' Q δ}) :
    0 < P {ω | pinchFirstEvent (D ω) W Tset Q' Q δ} := by
  obtain ⟨A, hAE, hAm, hAp⟩ :=
    cm_pinchFirstEvent_transfer hCM P hC hcirc hGFF f hf hfc hf0 _ _
      (firstEventFieldCertificate_of_measurable 𝔇 ξ α W Tset Q' Q δ P hC D f hD hmeas) hshift
  exact lt_of_lt_of_le hAp (measure_mono hAE)

end HarmonicBalls

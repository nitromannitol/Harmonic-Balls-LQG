import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11j.Geometry
import HarmonicBalls.FirstPass.S11e.Include
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.Proposed.LQG

/-!
# Assembly of the corrected Lemma 11.12

Route: the write-up's sections 3-4, with the local certificate interface of
the write-up's section 3.3, equation (3.9).

* `PinchLocalCertificateStmt` is a new step, kept as a named hypothesis. It asks for a
  Borel set `E` of local pairings on `B₇(0)` with positive probability on which the three whole-plane auxiliary events
  hold almost surely. The two-sided `PinchLocalDecoderStmt` of the first version (commit 697963b) is withdrawn: it was
  stronger than Lemma 11.12 needs, and `pinchFirstEvent` is not almost surely `σ(h|_{B₇})`-determined.
* `LQGMetricFieldAxioms` (`Proposed/LQG.lean:199`, Fact 2.2 I at `α₀ = α`) gives the
  Euclidean length property of the Weyl-shifted metric.
* `LQGMetricExponentPositive` (`FirstPass/Frozen/S11j.lean:94`, truth check TRUE) makes `ξ ≤ 0`
  vacuous, so the statement is proved for every real `ξ`.
* The inclusion is `pinchPointEvent_of_auxiliary_events` (`FirstPass/S11e/Include.lean:30`), already proved.

`PinchThirdEventFaithfulStmt` is not used. The file does not import `CertificateCanonical`, which consumes
`CorrectedLemma11_12Stmt`, so there is no cycle.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- NEW step, named hypothesis. Local certificate for
Lemma 11.12 (corrected paper lines 3236-3244; route Step 3.6, Step 4.2 and the positivity of Steps 4.3-4.5). For a fixed
buffered geometry, `γ ∈ (0,2)`, `ξ > 0` and `M > 0`, there is a Borel set `E` of pairings on `B₇(0)` such that for every
insertion `α < Q` and every model: `P[h^α|_{B₇} mod constants ∈ E] > 0`, and almost surely, if this event holds, then the
three auxiliary events of the true pair `(μ, D)` hold. The one-sided form is equation (3.9) of the write-up. -/
def PinchLocalCertificateStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E →
      (pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M ∧ pinchThirdEvent (D ω) V W δ)

/-- Lemma 11.12 in the corrected form (`CorrectedLemma11_12Stmt`, `FirstPass/S11i/Faithful.lean:56`) restricted to
`0 < ξ`. This is an intermediate statement; the full statement is `CorrectedLemma11_12Stmt`. -/
def CorrectedLemma11_12PosXiStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ₀ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball (0 : ℂ) 7)]
      {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E →
      pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0

/-- Lemma 11.12 (corrected) for `0 < ξ`, from the local certificate `PinchLocalCertificateStmt`, the length property
`LQGMetricFieldAxioms` (Fact 2.2 I, Proposed) at `α₀ = α`, and the inclusion `pinchPointEvent_of_auxiliary_events`. -/
theorem firstPass_11_12_corrected_posXi_of_cert
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hCert : PinchLocalCertificateStmt.{u}) :
    CorrectedLemma11_12PosXiStmt.{u} := by
  intro U V W T Q' Q δ hgeo hOmega γ ξ hγ hγ2 hξ M hM
  obtain ⟨E, hEm, hE⟩ := hCert U V W T Q' Q δ hgeo hOmega γ ξ hγ hγ2 hξ M hM
  refine ⟨E, hEm, ?_⟩
  intro α hα Ω _ P hC hcirc μ D hgff hμ hD
  obtain ⟨hSpos, hincl⟩ := hE α hα Ω P hC hcirc μ D hgff hμ hD
  refine ⟨localModConstField_measurable α hC (ball (0 : ℂ) 7) hEm, hSpos, ?_⟩
  have hgood : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) ∧ ∀ x y, 0 ≤ D ω x y := by
    obtain ⟨𝔇, h𝔇, hDω⟩ := hD
    filter_upwards [((hAx γ ξ α Ω P hC hcirc) hgff hγ hγ2 hα 𝔇 h𝔇).1, hDω] with ω hω hDωω
    have hEq : (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal) = D ω := by
      funext x y
      rw [← (hDωω x y).2, ENNReal.toReal_ofReal (hDωω x y).1]
    refine ⟨?_, fun x y => (hDωω x y).1⟩
    rw [← hEq]
    exact hω.2
  filter_upwards [hincl, hgood] with ω hω hgoodω hmem
  have haux := hω hmem
  exact pinchPointEvent_of_auxiliary_events (hgeo.toPinchPointProofConfiguration hgeo.U_nonempty)
    hgoodω.1 hgoodω.2 (μ ω) M haux.1 haux.2.1 haux.2.2

/-- Lemma 11.12 in the corrected form for every real `ξ` (`CorrectedLemma11_12Stmt`, `FirstPass/S11i/Faithful.lean:56`;
correction `[C43]`). For `0 < ξ` this is `firstPass_11_12_corrected_posXi_of_cert`. For `ξ ≤ 0` the hypothesis
`IsLQGMetricOfField` is impossible, since `LQGMetricExponentPositive` gives `0 < ξ` for every `IsLQGMetric`
, so the empty set serves as `E` and the implications hold vacuously. -/
theorem firstPass_11_12_corrected
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hCert : PinchLocalCertificateStmt.{u}) (hXi : LQGMetricExponentPositive) :
    CorrectedLemma11_12Stmt.{u} := by
  intro U V W T Q' Q δ₀ hgeo hOmega γ ξ hγ hγ2 M hM
  rcases lt_or_ge 0 ξ with hξ | hξ
  · obtain ⟨E, hEm, hE⟩ :=
      firstPass_11_12_corrected_posXi_of_cert hAx hCert U V W T Q' Q δ₀ hgeo hOmega γ ξ hγ hγ2 hξ M hM
    exact ⟨E, hEm, hE⟩
  · refine ⟨∅, MeasurableSet.empty, ?_⟩
    intro α _ Ω _ P hC hcirc μ D _ _ hD
    obtain ⟨𝔇, h𝔇, -⟩ := hD
    exact absurd (hXi γ ξ 𝔇 hγ hγ2 h𝔇) (not_lt.mpr hξ)

end HarmonicBalls

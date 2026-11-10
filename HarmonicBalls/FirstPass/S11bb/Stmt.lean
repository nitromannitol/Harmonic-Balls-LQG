import HarmonicBalls.FirstPass.S11m.Corrected11_12
import HarmonicBalls.FirstPass.S11m.LocalRule

/-!
# Decoded identification of the local certificate (fp-S11bb, STEP A; Lemma 11.12)

This file states the decoded identification `PinchDecodedIdentificationStmt` only. It is proved by the
owner of the decoding (z4) and consumed by `HarmonicBalls.S11bb.pinchLocalCertificate_of_identification`
(FirstPass/S11bb.lean), which proves the certificate `PinchLocalCertificateStmt` from it.

The identification is step 4 of `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` (equation (2), line 101;
Section 5, line 383; Section 6.1, line 414). For a buffered pinch geometry and parameters `γ ∈ (0,2)`, `ξ > 0`,
`M > 0`, it gives one Borel set `E` of pairings on `B₇(0)` such that, almost surely, the local field
`h^α|_{B₇(0)}` modulo constants lies in `E` if and only if the local certificate rule `pinchLocalRule` of the true
pair `(μ, D)` holds together with the two finiteness facts `SG_{3,6}(μ) ≠ ∞` and `μ(U) ≠ ∞`.

Names follow Armstrong–Kuusi–Mourrat (internal metric, Weyl scaling, decoded pairings) and Duplantier–Sheffield
(LQG measure `μ` and metric `D` of the insertion-`α` field). The universe `u` is that of `Corrected11_12.lean`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal
open HarmonicBalls.S11m.LocalRule

universe u

namespace HarmonicBalls
namespace S11bb

/-- Decoded identification of the local certificate (STEP A of fp-S11bb). For every buffered pinch geometry
`(U, V, W, T, Q', Q, δ)` with `{0} ∪ ∂B₅(0) ⊆ pinchOmegaGeom W Q δ`, and every `γ ∈ (0,2)`, `ξ > 0`, `M > 0`, there is
a measurable set `E` of pairings on `B₇(0)` such that, for every insertion `α < Q(γ)` and every whole-plane GFF model
with insertion-`α` LQG measure `μ` and LQG metric `D`, almost surely:
`localModConstField α h^ℂ B₇(0) ∈ E ↔ pinchLocalRule μ D W T Q' Q U V δ M ∧ SG_{3,6}(μ) ≠ ∞ ∧ μ(U) ≠ ∞`.
The same binders as `PinchLocalCertificateStmt` (`FirstPass/S11m/Corrected11_12.lean:40`). -/
def PinchDecodedIdentificationStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    ∀ᵐ ω ∂P, (localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
      (pinchLocalRule (μ ω) (D ω) W T Q' Q U V δ M ∧ annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ⊤ ∧ μ ω U ≠ ⊤))

end S11bb
end HarmonicBalls

import HarmonicBalls.Draft.Section11
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFrequency

/-!
# Local pinch certificate (Section 11, Lemma 11.12 and the form used by Lemma 11.13)

Written argument: `notes/sec11-proof/sec11-proof-r7.tex`, paragraph "Positive local pinch certificates"
(r7 lines 937–1037). For each exponent `α < lqgQ γ` the event `E(M) = E₁ ∩ E₂(M) ∩ E₃` is local in `B₇` and
invariant under adding a constant, is contained in the pinch event `Ĝ₁(0; M)`, and has positive probability.

* `Sec11LocalPinchCertificateStmt` states this local-certificate form as a single proposition. It quantifies over
  every `α < lqgQ γ`, as `ManyPinchScalesStmt` (Lemma 11.13, `HarmonicBalls/Draft/Section11.lean:259`) does.
* `pinchEventPositiveProbabilityStmt_of_localCertificate` shows that the certificate implies the frozen target
  `PinchEventPositiveProbabilityStmt` (Lemma 11.12, `HarmonicBalls/Draft/Section11.lean:246`), at `α₀ = 0`.

The upstream Section 11 modules use code by Leonardo Bonanno (`LatticeProb.Bonanno`), including the potential-theoretic
infrastructure behind the metric-field consumers.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- The local pinch certificate (written argument, r7 lines 937–1037), for every exponent `α < lqgQ γ`.
There is a pinch-point configuration `U, T, Q', Q`, chosen before all other parameters, such that for all
`0 < γ < 2`, `ξ`, every probability space carrying a whole-plane GFF `P` with LQG measure `μ` at exponent `α`
and LQG metric `D` at exponents `(ξ, α)`, and every `M > 0`, there is a set `E` of the field σ-algebra restricted
to `B₇` modulo additive constants (`Section6.fieldSigmaAlgebraModConst`), with `0 < P E`, on which the pinch
event `pinchPointEvent … M 1 0` holds. -/
def Sec11LocalPinchCertificateStmt : Prop :=
  ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
    IsLQGMetricOfField P γ ξ α hC D →
    ∀ M : ℝ, 0 < M → CorrectedLocalPinchCertificate P α hC μ D U T Q' Q M

/-- The local pinch certificate implies the frozen Lemma 11.12 target `PinchEventPositiveProbabilityStmt`:
at `α₀ = 0` the certificate gives a measurable inner witness of the original pinch event
(`correctedLocalPinchCertificate_innerWitness`), since `0 < lqgQ γ` for `0 < γ < 2`. -/
theorem pinchEventPositiveProbabilityStmt_of_localCertificate
    (h : Sec11LocalPinchCertificateStmt.{u}) : PinchEventPositiveProbabilityStmt.{u} := by
  obtain ⟨U, T, Q', Q, hc, hcert⟩ := h
  refine ⟨U, T, Q', Q, hc, ?_⟩
  intro γ ξ hγ hγ' Ω _ P hC hcirc μ D hgff hμ hD M hM
  have hQ : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ) (half_pos hγ)
  exact correctedLocalPinchCertificate_innerWitness P 0 hC hcirc μ D U T Q' Q M hgff
    (hcert γ ξ hγ hγ' 0 hQ Ω P hC hcirc μ D hgff hμ hD M hM)

#print axioms pinchEventPositiveProbabilityStmt_of_localCertificate

end HarmonicBalls

import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferDerived
import HarmonicBalls.Proposed.LQG

/-!
# Canonical decoder identity (MQ-lh-29, input (c) of the canonical domination)

The α₀-LQG measure `μ` of the whole-plane GFF `hcirc` is almost surely the decoder of the
canonical profile: `μ ω = decoder canonicalTest γ α₀ (canonicalSel (posPart (hcirc ω)))`.
This is the missing identity (c) of the canonical rooted domination (`ShiftedDecoderNullTransferCanonicalStmt`
in `RootedShiftedNullTransferDerived.lean`), which takes it as the hypothesis `∀ᵐ ω ∂P, μ ω = ...`.

The statement `CanonicalDecoderIdentityStmt` copies the hypotheses of `ShiftedDecoderNullTransferCanonicalStmt`
(the whole-plane GFF, `0 < γ < 2`, `α₀ < Q(γ)`, the α₀-LQG measure, and the existence hypothesis
`LQGMeasureExistence P γ α₀`, which the proof does not use). The Duplantier-Sheffield (arXiv:0808.1560)
convergence of dyadic approximations identifies the limit with the decoder on the convergence locus.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- **Canonical decoder identity** (MQ-lh-29, input (c)). For every whole-plane GFF `hcirc` with
`0 < γ < 2`, `α₀ < Q(γ)`, and every α₀-LQG measure `μ` of `hcirc`, the measure `μ` is almost surely the
canonical decoder `decoder canonicalTest γ α₀` applied to the canonical selector of the positive-radius part of
`hcirc`. -/
def CanonicalDecoderIdentityStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → LQGMeasureExistence P γ α₀ hC hcirc →
    ∀ᵐ ω ∂P, μ ω = ProfileDecoderDerived.decoder canonicalTest γ α₀ (canonicalSel (posPart (hcirc ω)))

end HarmonicBalls

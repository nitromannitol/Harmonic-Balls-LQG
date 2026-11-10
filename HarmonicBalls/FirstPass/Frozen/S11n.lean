import HarmonicBalls.FirstPass.S11n

/-!
# Frozen existence of common canonical LQG decoders (Step 15 of `CHATGPT-11-13-proof.md`)

One EXTERNAL input for the pull-back of the canonical statement to an arbitrary whole-plane GFF model. Its witnesses
are the common decoders `Dμ`, `Dd` on the canonical field space, used in `LQGCanonicalIdentificationStmt`
(`FirstPass/S11n.lean`).
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- FIRST-PASS FROZEN, EXTERNAL (operator ruling 23:53 UTC on B1; truth check TRUE, ChatGPT 23:53 UTC,
`notes/fp-gaps/CHATGPT-n1-B1-canonical-decoders.md`, Verdict and section 1). For every `γ ∈ (0, 2)`, every `ξ ∈ ℝ` and
every `α₀ < Q_γ`, there are common canonical decoders `Dμ : CanonSpace → Measure ℂ` and `Dd : CanonSpace → ℂ → ℂ → ℝ`
for which `LQGCanonicalIdentificationStmt` holds: for every whole-plane GFF model, every LQG measure `μ` and every LQG
metric `D` of the field `h^ℂ - α₀ log|·|`, almost surely `μ = a • Dμ (alphaCanon α₀ hC)` and
`D = b * Dd (alphaCanon α₀ hC)` for constants `a, b > 0`.

Sources: the measure decoder from the mean-zero local decoders, Duplantier-Sheffield arXiv:0808.1560v2; the metric
uniqueness up to a deterministic factor, Gwynne-Miller arXiv:1905.00383v3, Theorem 1.2, p. 6; the inserted metric,
DFGPS arXiv:1905.00380v2; the reconstruction of the normalised field from mean-zero observations (ruling, section 2.2).
The parameter `ξ` is free: Gwynne-Miller Theorem 1.2 is displayed at `ξ = γ/d_γ`, and section 5.2 of the ruling reduces the
free-`ξ` form to that value (for a value with no metric the metric clause is vacuous).
Used by: `correctedLemma11_13_of_existence` (`HarmonicBalls/FirstPass/S11n/Existence.lean`). -/
def LQGCanonicalDecodersExistStmt : Prop :=
  ∀ (γ ξ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ),
      S11n.LQGCanonicalIdentificationStmt.{u} γ ξ α₀ Dμ Dd

end HarmonicBalls

import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement

/-!
# First-pass frozen input: local LQG metric reconstruction (hN2 / hR, owner n3, fp-S11-13-count)

`LocalMetricReplacementFrozen` is the FIRST-PASS FROZEN wrapper of `LocalMetricReplacementStmt`
(`HarmonicBalls/FirstPass/S11r/LocalMetricReplacement.lean:58`). The wrapper is the binder `hN2` of the counted Lemma 11.13
assembly (`HarmonicBalls/FirstPass/S11i/Final11_13.lean`), and it also supplies the metric replacement `hR` of the
insertion-zero constructions. Operator decision (2026-11-10 19:00 UTC): freeze it now; the derivation goes to phase 2.

The statement is an EXTERNAL fact about general LQG metrics (local metric reconstruction, with the scalar absorbed in the
positive constant), not a statement about harmonic balls, clusters or odometers of this paper.

Truth status. Codex Sol, 2026-11-10, `notes/fp-gaps/CODEX-hN2-sol-20261110.md`: no counterexample was found, and the
quantifier structure of the displayed type is as intended. That note does not certify the exact Lean truth
("TRUE exactly as typed" is not established); its verdict is DERIVE with a route, and the provider remains open.
Derivation route (phase 2): recorded in that note; its open step is the off-root physical comparison.

Locators (taken from the note's table; not re-verified against the sources in this file):
* metric measurability, locality, Weyl scaling: Gwynne–Miller, arXiv:1905.00383v3, §1.2, pp. 5–6, axioms II–III;
* existence and uniqueness: Gwynne–Miller, arXiv:1905.00383v3, Theorem 1.2, p. 6 (uniqueness discussion p. 7);
* proper-domain metrics: Gwynne–Miller, arXiv:1905.00383v3, Remark 1.5, p. 8;
* logarithmic insertions: Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380v2, Theorem 1.10, p. 10;
  Proposition 3.17, p. 43, equation (3.56).
-/

namespace HarmonicBalls

/-- **FIRST-PASS FROZEN (EXTERNAL, general LQG).** The local metric replacement of `LocalMetricReplacementStmt`
(`S11r/LocalMetricReplacement.lean:58`), with the same binders and conclusion. Truth: no counterexample, quantifier
structure checked (Codex Sol 2026-11-10, `notes/fp-gaps/CODEX-hN2-sol-20261110.md`); exact Lean truth not certified there.
Derivation route recorded there (phase 2). -/
def LocalMetricReplacementFrozen.{u} (γ ξ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : Prop :=
  LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂

end HarmonicBalls

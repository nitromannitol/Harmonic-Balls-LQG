import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement

/-!
# Frozen input: local LQG metric reconstruction (hN2 / hR)

`LocalMetricReplacementFrozen` is the FROZEN wrapper of `LocalMetricReplacementStmt`
(`HarmonicBalls/FirstPass/S11r/LocalMetricReplacement.lean:58`). The wrapper is the binder `hN2` of the counted Lemma 11.13
assembly (`HarmonicBalls/FirstPass/S11i/Final11_13.lean`), and it also supplies the metric replacement `hR` of the
insertion-zero constructions. The derivation is deferred.

The statement is an EXTERNAL fact about general LQG metrics (local metric reconstruction, with the scalar absorbed in the
positive constant), not a statement about harmonic balls, clusters or odometers of this paper.

Truth status: no counterexample was found, and the
quantifier structure of the displayed type is as intended. The exact Lean truth
("TRUE exactly as typed" is not established); its verdict is DERIVE with a route, and the provider remains open.
Derivation route: its open step is the off-root physical comparison.

Locators (not re-verified against the sources in this file):
* metric measurability, locality, Weyl scaling: Gwynne–Miller, arXiv:1905.00383v3, §1.2, pp. 5–6, axioms II–III;
* existence and uniqueness: Gwynne–Miller, arXiv:1905.00383v3, Theorem 1.2, p. 6 (uniqueness discussion p. 7);
* proper-domain metrics: Gwynne–Miller, arXiv:1905.00383v3, Remark 1.5, p. 8;
* logarithmic insertions: Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380v2, Theorem 1.10, p. 10;
  Proposition 3.17, p. 43, equation (3.56).
-/

namespace HarmonicBalls

/-- **FROZEN (EXTERNAL, general LQG).** The local metric replacement of `LocalMetricReplacementStmt`
(`S11r/LocalMetricReplacement.lean:58`), with the same binders and conclusion. Truth: no counterexample, quantifier
structure checked; exact Lean truth not certified there.
Derivation route recorded there (phase 2). -/
def LocalMetricReplacementFrozen.{u} (γ ξ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) : Prop :=
  LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂

end HarmonicBalls

# Metric normalizer comparison: two normalizer families for one observable

Task `weak-metric-normalizer-family-comparison` (worker z6). Lean file:
`HarmonicBalls/Proofs/GFF/MetricNormalizerComparison.lean` (module `HarmonicBalls.Proofs.GFF.MetricNormalizerComparison`).

**Status.** Proved, with no literature input and no new hypothesis beyond the abstract tightness assumptions below.
`lc` and `lb` pass; the four main theorems print only `propext`, `Classical.choice`, `Quot.sound`. The file is
independent of any normalized annulus law, of any Pfeffer Proposition and of any physical dimension identity.
It imports Mathlib only.

## 1. Statements

Setting: `Ω` a measurable space, `P` a probability measure, `X : ℝ → Ω → ℝ≥0∞` one family of observables indexed by the
scale `r`, and `c, c' : ℝ → ℝ` two deterministic normalizers, positive on `(0, ∞)`.

* `normWindow X c M r = {ω | M⁻¹ ≤ X r ω / c r ∧ X r ω / c r ≤ M}` (in `ℝ≥0∞`, with `ofReal` coercions).
* `NormWindowTight P X c`: for every `ε ∈ (0,1)` there is `M > 0` with `P(normWindow X c M r) ≥ 1 - ε` for all `r > 0`.
  The window is invariant under `x ↦ x⁻¹`, so this is tightness of `X_r / c_r` and of `c_r / X_r`.
* `UniformLogExponent c a`: for every `η > 0` there is `δ₀ > 0` with
  `|log (c (δ r) / c r) / log δ - a| ≤ η` for all `δ ∈ (0, δ₀)`, `δ < 1`, and all `r > 0`. This is the uniform form of
  (1.10) in Pfeffer (arXiv:2104.04020v3, Proposition 1.9): `c_{δr}/c_r = δ^{a + o_δ(1)}`, the `o(1)` uniform in `r`.

Theorems (all in `namespace HarmonicBalls`):

| Lean name | Statement |
|---|---|
| `measurableSet_normWindow` | `Measurable (X r)` implies the window is measurable. |
| `toReal_window` | An `ℝ≥0∞` window for `x / c` (with `c > 0`) forces `x ≠ ∞` and is the real window `M⁻¹ ≤ x.toReal / c ≤ M`. |
| `nonempty_inter_of_prob_ge` | Two measurable events of probability `≥ 1 - ε`, `ε < 1/2`, meet. |
| `ratio_bounds` | `u ∈ [M₁⁻¹, M₁]`, `v ∈ [M₂⁻¹, M₂]` imply `u / v ∈ [(M₁M₂)⁻¹, M₁M₂]`. |
| `normalizer_ratio_bounded` | Both families `NormWindowTight` with the same measurable `X` give `K > 0` with `K⁻¹ ≤ c' r / c r ≤ K` for all `r > 0`. |
| `abs_log_le_abs_log_of_bounds` | `K⁻¹ ≤ ρ ≤ K` implies `|log ρ| ≤ |log K|`. |
| `uniformLogExponent_of_comparison` | Under the uniform comparison `K⁻¹ ≤ c'/c ≤ K`, `UniformLogExponent c a` implies `UniformLogExponent c' a`. |
| `comparison_symm` | The reverse comparison `K⁻¹ ≤ c/c' ≤ K`. |
| `uniformLogExponent_stable` | Under the two window hypotheses, `UniformLogExponent c a → UniformLogExponent c' a`. |
| `uniformLogExponent_iff` | Under the two window hypotheses, `UniformLogExponent c a ↔ UniformLogExponent c' a`. |

## 2. Proof route

1. **Windows meet.** Take `ε = 1/4` in both tightness hypotheses, with constants `M₁` (for `c`) and `M₂` (for `c'`).
   Each window has probability `≥ 3/4`. If the two windows were disjoint, the second would lie in the complement of the
   first, so `3/4 + 3/4 ≤ P(A) + P(B) ≤ P(A) + P(Aᶜ) = 1`, which is false. Hence they meet at some `ω`, for each fixed `r > 0`.
   (`nonempty_inter_of_prob_ge`; measurability of the windows is needed here and comes from `Measurable (X r)`.)
2. **Positivity and finiteness come from the windows.** At `ω`, `X r ω / c r ≥ M₁⁻¹ > 0`, so `X r ω ≠ 0`, and
   `X r ω / c r ≤ M₁ < ∞`, so `X r ω ≠ ∞`. The real number `x = (X r ω).toReal` satisfies `M₁⁻¹ ≤ x / c r ≤ M₁` and
   `M₂⁻¹ ≤ x / c' r ≤ M₂` (`toReal_window`). No positivity or finiteness hypothesis on `X` is assumed.
3. **Ratio.** `c' r / c r = (x / c r) / (x / c' r)` since `x ≠ 0`. Then `ratio_bounds` gives
   `K := M₁ M₂` with `K⁻¹ ≤ c' r / c r ≤ K`. The constant does not depend on `r`, because each window is uniform in `r`.
4. **Exponent.** Put `ρ = c'/c`, so `c'_{δr}/c'_r = (c_{δr}/c_r) · (ρ(δr)/ρ(r))`. Hence
   `log(c'_{δr}/c'_r) = log(c_{δr}/c_r) + D`, with `D = log ρ(δr) - log ρ(r)` and `|D| ≤ 2|log K|` for all `r`
   (`abs_log_le_abs_log_of_bounds`). Given `η`, take `δ₁ = exp(-4|log K|/η)`. For `δ < δ₁` one has `|log δ| ≥ 4|log K|/η`,
   so `|D / log δ| ≤ η/2`. Combine with the `η/2` bound for `c`, and the triangle inequality, to get `η`.
   The bound is uniform in `r` because the constant `K` is.

## 3. What is assumed, and what is not

Assumed (abstract hypotheses, all explicit in the theorem statements):

* `IsProbabilityMeasure P`;
* `Measurable (X r)` for each `r` (a random observable);
* `NormWindowTight P X c` and `NormWindowTight P X c'` (uniform tightness of the normalized observable and its reciprocal, for the
  same `X`);
* positivity `0 < c r`, `0 < c' r` for `r > 0`.

Not assumed: a law of any LQG metric or annulus; a Pfeffer Proposition (`PfefferAxiomVScale`, `PfefferBackgroundScaling` and
`PfefferTightAcrossScales` in `HarmonicBalls/Proposed/PfefferMetricScaling.lean` are **not** imported); a physical dimension
identity; any positivity or finiteness of `X`.

Correspondence (documentation only, not an import): `NormWindowTight P X c` is the window form of Axiom V's tightness
(`PfefferTightAcrossScales`, `Proposed/PfefferMetricScaling.lean:84-87`), applied to the normalized observable `X_r / c_r`.
`UniformLogExponent c a` is the uniform form of (1.10) and matches the exponent notion of
`HarmonicBalls/Proofs/GFF/MetricExponentScaling.lean` (`exponent_eq_of_asymptotic_power`).
The result does not say whether Pfeffer's normalizers satisfy the window hypothesis: that is a separate target.

## 4. Checks

* `lc HarmonicBalls/Proofs/GFF/MetricNormalizerComparison.lean`: CHECK OK (with `warningAsError`).
* `lb HarmonicBalls.Proofs.GFF.MetricNormalizerComparison`: BUILD OK.
* `#print axioms` (at the end of the file, as in `MetricAnnulusScaleLaw.lean`): for `normalizer_ratio_bounded`,
  `uniformLogExponent_of_comparison`, `uniformLogExponent_stable`, `uniformLogExponent_iff`, each prints
  `[propext, Classical.choice, Quot.sound]`.
* Code-level scan for `sorry`, `admit`, `native_decide`, `maxHeartbeats`, `axiom` declarations, `opaque`, `extern`,
  `implemented_by`: no match.

## 5. Credit

The whole-plane GFF and LQG carriers to which this comparison is applied are due to Leonardo Bonanno, through his
Lattice-Probability library (the `lean-v4.35` line pinned in `lakefile.lean`). The Lean file credits him in its module
docstring. It consumes no declaration from that library, so no `LatticeProb` name appears in it.

## 6. Open points

* No consumer yet. A future use would discharge `NormWindowTight` for the actual annulus normalizers. The nearest existing
  result is `normalizedAcross_tight` in `HarmonicBalls/Proofs/GFF/MetricAnnulusScaleLaw.lean:375`. Whether its normalizers
  match the hypothesis here is not checked in this task.

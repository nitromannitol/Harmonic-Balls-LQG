# Audit: WeightedFourierDuality (task `sec11-weighted-fourier-duality`)

Owner: z3. File: `HarmonicBalls/Proofs/Sec11/ClosureScales/WeightedFourierDuality.lean` (new, 207 lines, namespace
`HarmonicBalls`, imports `Mathlib` only, not imported by `HarmonicBalls.lean`, which is read-only for this task).

Status. `lc` CHECK OK, zero warnings (`warningAsError`; final log `025045-1985262`). `lb` BUILD OK (final log `025150-2097123`).
Printed axioms of the public declarations: `[propext, Classical.choice, Quot.sound]` for each of the 12 declarations of the file
(scratch file `/tmp/z3-weighted-axioms.lean` on the sandbox, outside the repository; log `025356-2322007`). Raw scan of the file, comments included, for `sorry`, `axiom`, `admit`, `native_decide`,
`unsafe`, `extern`, `implemented_by`, `heartbeat`, `set_option`, `opaque`, `Bonanno`, `Lattice`: 0 hits. No new carrier,
distribution, Sobolev space, decoder, standing Step, or numbered closure is introduced.

## 1. Written source and scope

- Source: `notes/sec11-proof/sec11-proof-r10.tex`, lines 1075-1087 (weighted square-summable Fourier coefficients that
  define an `H^{-2}` distribution by Fourier partial sums). This file formalizes only the weighted Cauchy-Schwarz
  summation prerequisite of that step.
- Not formalized here: the distribution itself, its reconstruction, the support and gluing conditions, the Borel
  decoder, and the closure `R`. No declaration in this file is a consumer of those objects.
- Literal carrier: `ℤ × ℤ` (the frequency carrier of `CutoffFourierSummability.lean`).
- Literal weight: `(1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)`, written inline in every statement (no new `def`).
  It is the expression of `CutoffFourierSummability.lean:67` (`frequencyWeight_nonneg`). The power `w(k)^(-1)` is
  written `(w k)⁻¹` (`zpow_neg_one`).
- Sine/cosine coordinates: `a, b` are the cosine and sine coefficient families of the first expansion, `u, v` those of
  the second; the pairing series is `∑_k (a k * u k + b k * v k)`.

## 2. Declarations (binders and statements)

Line numbers refer to `WeightedFourierDuality.lean`. `x k = a k * u k + b k * v k`,
`F k = (1 + k.1² + k.2²)^(-2) * (a k ^ 2 + b k ^ 2)`, `G k = ((1 + k.1² + k.2²)^(-2))⁻¹ * (u k ^ 2 + v k ^ 2)`.

| Line | Declaration | Binders | Conclusion |
|---|---|---|---|
| 38 | `abs_mul_add_mul_le_sqrt_mul_sqrt` | `{w a b u v : ℝ} (hw : 0 < w)` | `\|a u + b v\| ≤ √(w (a²+b²)) √(w⁻¹ (u²+v²))` |
| 49 | `pairing_pointwise` | `{w a b u v : ι → ℝ} (hw : ∀ i, 0 < w i)` | the pointwise bound, `0 ≤ F i`, `0 ≤ G i` |
| 59 | `summable_sqrt_mul_sqrt_and_tsum_le` | `{F G : ι → ℝ} (hF0) (hG0) (hF : Summable F) (hG : Summable G)` | `Summable (√F √G)` and `∑' √F √G ≤ √(∑' F) √(∑' G)` |
| 78 | `sum_abs_le_of_pointwise` | `{x F G} (hx : ∀ i, \|x i\| ≤ √(F i) √(G i)) (hF0) (hG0) (S : Finset ι)` | `∑_S \|x\| ≤ √(∑_S F) √(∑_S G)` |
| 84 | `summable_and_tsum_le_of_pointwise` | `{x F G} (hx) (hF0) (hG0) (hF) (hG)` | `Summable \|x\|`, `Summable x`, `\|∑' x\| ≤ √(∑' F) √(∑' G)` |
| 98 | `abs_sub_le_sqrt_of_pointwise` | `[DecidableEq ι] {x F G} (hx) (hF0) (hG0) {S T : Finset ι} (hST : S ⊆ T)` | `\|∑_T x - ∑_S x\| ≤ √(∑_T F - ∑_S F) √(∑_T G - ∑_S G)` |
| 114 | `exists_finset_abs_sub_le_of_pointwise` | `[DecidableEq ι] {x F G} (hx) (hF0) (hG0) (hF) (hG) {ε} (hε : 0 < ε)` | `∃ R, ∀ S T, R ⊆ S → S ⊆ T → \|∑_T x - ∑_S x\| ≤ ε` |
| 148 | `frequencyWeight_pos` | `(k : ℤ × ℤ)` | `0 < (1 + k.1² + k.2²)^(-2:ℤ)` |
| 155 | `weightedFourier_duality` | `(a b u v : ℤ × ℤ → ℝ) (ha : Summable F) (hu : Summable G)` | `Summable \|x\|`, `Summable x`, `\|∑' x\| ≤ √(∑' F) √(∑' G)` |
| 170 | `weightedFourier_finite_sum_abs_le` | `(a b u v) (S : Finset (ℤ × ℤ))` | `∑_S \|x\| ≤ √(∑_S F) √(∑_S G)` |
| 181 | `weightedFourier_finite_tail_le` | `(a b u v) {S T : Finset (ℤ × ℤ)} (hST : S ⊆ T)` | `\|∑_T x - ∑_S x\| ≤ √(∑_T F - ∑_S F) √(∑_T G - ∑_S G)` |
| 195 | `weightedFourier_cauchy` | `(a b u v) (ha : Summable F) (hu : Summable G) {ε} (hε : 0 < ε)` | `∃ R : Finset (ℤ × ℤ), ∀ S T, R ⊆ S → S ⊆ T → \|∑_T x - ∑_S x\| ≤ ε` |

The hypotheses are only the two summability conditions on the weighted series, the positivity of the weight (proved, not
assumed), and `ε > 0`. No hypothesis is a conclusion, and no literature input is assumed.

## 3. Mathematics and Mathlib providers

- Pointwise (line 38): `(a u + b v)² ≤ (a²+b²)(u²+v²) = [w(a²+b²)] [w⁻¹(u²+v²)]`, using `w w⁻¹ = 1` (`w > 0`); the
  identity `(a²+b²)(u²+v²) - (au+bv)² = (av - bu)²` is the `nlinarith` hint.
- Finite sums (line 78): `Real.sum_sqrt_mul_sqrt_le` (`Mathlib/Analysis/Real/Sqrt.lean:506`).
- Infinite sums (line 59): Hölder with exponents `2, 2`,
  `Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg` with `Real.HolderConjugate.two_two`
  (`Mathlib/Analysis/MeanInequalities.lean:972`, `Mathlib/Basic/Real/ConjExponents.lean:137`).
- Absolute and signed series (line 84): comparison (`Summable.of_nonneg_of_le`), `Summable.of_norm`,
  `norm_tsum_le_tsum_norm`.
- Finite tails (line 98): `Finset.sum_sdiff` for `T \ S`, then line 78 on `T \ S`.
- Cauchy criterion (line 114): `summable_iff_vanishing_norm` (`Mathlib/Analysis/Normed/Group/InfiniteSum.lean:56`).
  `T \ S` is disjoint from every finite set contained in `S`, so `‖∑_{T\S} F‖ < ε` and `‖∑_{T\S} G‖ < ε`, and the
  tail bound gives `√(∑_{T\S} F) √(∑_{T\S} G) ≤ √ε √ε = ε`.
- Route rejected: `summable_iff_cauchySeq_finset` with `Metric.cauchySeq_iff` timed out (uniform-structure defeq at
  elaboration of the argument, `isDefEq` heartbeat limit); the vanishing-norm form avoids it.

## 4. Why strict positivity, and the provider

`frequencyWeight_nonneg` (`CutoffFourierSummability.lean:67`) gives only `0 ≤ w`. Strict positivity is needed: where
`w k = 0`, both `F k` and `G k` vanish for every `a, b, u, v`, and the pointwise bound fails. The file therefore proves
`frequencyWeight_pos` (`zpow_pos` with `0 < 1 + k.1² + k.2²`). No other provider of `CutoffFourierSummability.lean` or
`FourierFinitenessMeasurable.lean` is used, and no circle-average declaration is used.

## 5. Import closure, credit, consumers

- Imports: `Mathlib` only. The file imports no `HarmonicBalls` module, so no `Defs`, `Draft`, `External`, `Proposed`,
  or `Steps` declaration is in its closure.
- Credit: the file consumes no Lattice-Probability module and no Bonanno content, so no Bonanno credit line is required
  and none is written. The raw scan finds no `Bonanno` or `Lattice` token.
- Consumers: none in the repository. The intended consumer is the `H^{-2}` distribution step of
  `sec11-proof-r10.tex:1075-1087`, which this file does not define.

## 6. Scope flags

- `tsum` in Lean is `0` for a non-summable family. The bound is stated under the two summability hypotheses, so it is
  meaningful.
- The Cauchy statement is the Cauchy criterion for finite partial sums over `ℤ × ℤ`. It is not a convergence statement
  for a distribution.
- The file does not define any distribution, Sobolev norm, or reconstruction.

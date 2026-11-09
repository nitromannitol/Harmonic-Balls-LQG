# Audit: SmoothCircleAverageRate (task sec11-smooth-circle-average-linear-rate)

File: `HarmonicBalls/Proofs/Sec11/ClosureScales/SmoothCircleAverageRate.lean`, namespace `HarmonicBalls.SmoothCircleAverageRate`.
Worker z3 (Claude Haiku 5.5). New file, no existing declaration edited.

## Status

- lc: CHECK OK with `-DwarningAsError=true`, zero warnings (log `033433-2291112`).
- lb: BUILD OK for `HarmonicBalls.Proofs.Sec11.ClosureScales.SmoothCircleAverageRate` (log `033455-2327104`).
- Printed axioms, all six declarations: `[propext, Classical.choice, Quot.sound]` (probe file outside the repository, not committed).
- Raw scan, comments included (case-insensitive): sorry, axiom, admit, native, unsafe, extern, implemented_by, heartbeat, maxRecDepth, set_option, opaque, bonanno, lattice, reduceBool, decide: 0 hits.

## Literal statements

`φ : ℂ → ℝ`, `hφ : IsTestFunction univ φ`. `Real.circleAverage` is Mathlib's average over the circle.

1. `exists_lipschitz_of_isTestFunction (hφ) : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℂ, |φ y - φ x| ≤ L * ‖y - x‖`
2. `abs_circleAverage_sub_le_of_lipschitz (hφ) {L} (hL : ∀ x y : ℂ, |φ y - φ x| ≤ L * ‖y - x‖) {r} (hr : 0 < r) (x : ℂ) : |Real.circleAverage φ x r - φ x| ≤ L * r`
3. `exists_abs_circleAverage_sub_le (hφ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : ℂ, |Real.circleAverage φ x r - φ x| ≤ C * r`
4. `exists_integral_sq_circleAverage_sub_le (hφ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∫ x, (Real.circleAverage φ x r - φ x) ^ 2 ≤ C * r ^ 2`
5. `circleTestIntegral_second_moment_le_schur {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) (hφ : IsTestFunction univ φ) {r M B : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hzero : ∀ x : ℂ, x ∉ ball (0 : ℂ) M → Real.circleAverage φ x r - φ x = 0) (hB : ∀ x : ℂ, |Real.circleAverage φ x r - φ x| ≤ B) : ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P ≤ (2 * kernelBoxConst M).toReal * ∫ x, (Real.circleAverage φ x r - φ x) ^ 2`
6. `exists_second_moment_circleTestIntegral_le (hφ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ r : ℝ, 0 < r → r ≤ 1 → ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P ≤ C * r ^ 2`

Binders and carriers:
- `IsTestFunction U φ` is `ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U` (`HarmonicBalls/Defs/Laplacian.lean:47`), with `U = univ`.
- `IsWholePlaneGFF P hC hcirc` is `HarmonicBalls/Defs/GFF.lean:93`. It does not assume a probability measure. `hC ω φ` is the pairing and `hcirc ω r z` the circle average.
- The circle-average test integral `∫ w, hcirc ω r w * φ w` uses Lebesgue measure on `ℂ`.
- `Real.circleAverage` is `Mathlib/MeasureTheory/Integral/CircleAverage.lean:55`. `circleAverage_eq_Ioc` (`CircleTestFubiniLimit.lean:60`) gives `(2π)⁻¹ ∫_{(0,2π]} φ(circleMap x r θ) dθ`.
- `kernelBoxConst M : ℝ≥0∞` is `RouteAKernelBox.lean:82`, finite by `kernelBoxConst_lt_top` (`RouteAKernelBox.lean:87`). So `.toReal` is the finite real constant and no value is lost.
- The task's "Type*" is the universe variable `u` in statement 6. The bound holds for every `Ω : Type u`.
- The constants in 3, 4 and 6 are existential. They are `L`, `L² · vol(ball 0 M).toReal` and `(2 · kernelBoxConst M).toReal · C₂`, and they depend only on `φ` (through `L` and `M`), not on `Ω`, `P`, `hC` or `hcirc`.

## Providers (sorry-free, committed; each commit is an ancestor of `b125d07`, checked with `git merge-base --is-ancestor`)

| Provider | Location | Last commit |
|---|---|---|
| `CircleTestFubini.norm_circleAverage_sub_le` | `ClosureScales/CircleAverageSmoothTestConvergence.lean:53` | b80b997 |
| `CircleTestFubini.isTestFunction_univ_circleAverage` | `ClosureScales/CircleTestFubiniLimit.lean:142` | 2e35bf4 |
| `CircleTestIntegralL2Limit.exists_ball_circleAverage_sub_eq_zero` | `ClosureScales/CircleTestIntegralL2Limit.lean:187` | 01847af |
| `CircleTestIntegralL2Limit.integral_sq_le_of_bound` | `ClosureScales/CircleTestIntegralL2Limit.lean:206` | 01847af |
| `CircleTestIntegralL2Limit.isTestFunction_univ_sub` | `ClosureScales/CircleTestIntegralL2Limit.lean:167` | 01847af |
| `IsWholePlaneGFF.integral_sq_sub_pairing` | `ClosureScales/CircleTestIntegralL2Limit.lean:261` | 01847af |
| `IsWholePlaneGFF.ae_integral_circle_mul_eq_pairing_circleAverage` | `ClosureScales/GaussianCircleTestIntegral.lean:507` | facb52b |
| `abs_wholePlaneGFFCov_pairing_le` | `ClosureScales/RouteAKernelBox.lean:287` | 83246d2 |
| `kernelBoxConst_lt_top` | `ClosureScales/RouteAKernelBox.lean:87` | 83246d2 |

Mathlib: `Convex.norm_image_sub_le_of_norm_fderiv_le` (`Analysis/Calculus/MeanValue.lean:500`, inside `namespace Convex` from line 411); `HasCompactSupport.fderiv` (`Analysis/Calculus/FDeriv/Const.lean:389`, used with `(𝕜 := ℝ)`, as in `Sec8/OuterCutoff.lean:64`); `ContDiff.continuous_fderiv` (`Analysis/Calculus/ContDiff/Defs.lean:1272`); `Continuous.bounded_above_of_compact_support`; `norm_circleMap_zero`; `circleMap_sub_center`.

## Proof route

1. Lipschitz (statement 1): `φ` is `C¹` with compact support. `fderiv φ` is continuous with compact support, hence bounded. The mean value inequality on the convex set `ℂ` gives `L := max (sup ‖Dφ‖) 0`.
2. Circle bound (statement 2): on each circle, `|φ(circleMap x r θ) - φ x| ≤ L · ‖circleMap x r θ - x‖ = L r`. `norm_circleAverage_sub_le` then gives `|φ_r(x) - φ x| ≤ L r` for every `x` and `r > 0`.
3. Pointwise rate (statement 3): take `C = L`.
4. `L²` rate (statement 4): for `0 < r ≤ 1` the integrand vanishes off the fixed ball `B(0, M)` (`exists_ball_circleAverage_sub_eq_zero`). `integral_sq_le_of_bound` with `δ = L r` gives `∫ ≤ (L r)² vol(B(0,M))`.
5. Schur step (statement 5): the a.s. identity `∫ h^ℂ_r φ = h^ℂ(φ_r)` turns the left side into `E[(h^ℂ(φ_r) - h^ℂ(φ))²]`. `integral_sq_sub_pairing` writes this as the covariance kernel at the fixed test `φ_r - φ`. `abs_wholePlaneGFFCov_pairing_le` bounds it by `(2 · kernelBoxConst M).toReal · ∫ (φ_r - φ)²`. Its constant does not depend on `B`, so the choice `B = C₁ r` from statement 3 is harmless.
6. Export (statement 6): combine 5 and 4 with `C = (2 · kernelBoxConst M).toReal · C₂`.

## Credit (Leonardo Bonanno, Lattice-Probability port)

- The import closure was computed by a breadth-first search over `^import` lines starting from the four `ClosureScales` providers. It has 23 `HarmonicBalls` modules and no import outside Mathlib and `HarmonicBalls`. So no Lattice-Probability module is imported.
- The only file in the closure that names Bonanno or lattice is `ClosureScales/MollifiedContinuousCircleLimit.lean:30`, which states that it uses no Lattice-Probability declaration.
- Conclusion: this file consumes nothing from the pinned port and carries no Bonanno credit line. If the operator classifies it as a consumer, the credit must be added through the pinned port.

## Proposed inputs

- `CircleTestFubiniLimit.lean:7` imports `HarmonicBalls.Proposed.DuplantierMillerSheffield`, so that module is in the closure.
- None of the six statements takes a Proposed hypothesis. Their only hypotheses are `hφ`, `hgff` and the bounds `hzero`, `hB`. The printed axioms are the standard three.

## Remaining consumers and scope

- No file in the repository consumes these declarations yet. The new file is not imported by `HarmonicBalls.lean`.
- Not claimed: a.s. reconstruction of the circle-average field; any Borel, full-dyadic or carrier statement; any standing Step; any E56 closure; any numbered result closure.
- No new carrier, no literature admission, no hidden conclusion-as-hypothesis, no physical exponent, no metric moment.

# Audit: CircleAverageSmoothTestConvergence (task sec11-circle-average-smooth-test-convergence)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleAverageSmoothTestConvergence.lean` (new, 187 lines),
namespace `HarmonicBalls.CircleTestFubini`. Imports `Defs.Laplacian`, `RouteACircleSmooth`, `CircleTestFubiniLimit`.

Source (fleet paths, not repository paths): `notes/sec11-proof/sec11-proof-r10.tex` lines 1046–1062 (the tests are
`φ * σ_r` and "`φ*σ_r → φ` in the test-function topology") and lines 1353–1378 ("one fixed compact enlargement of
that support"; "As `r↓0`, the tests `φ*σ_{r,0}` converge to `φ` in the smooth test topology"). The round-9 audit row
`notes/sec11-proof/AUDIT-r9.md:17` (TeX 999–1025) relies on this convergence for the shifted reconstruction. The
written text does not define the smooth test topology; the Lean statements below prove the literal criterion it uses:
one fixed compact support plus uniform convergence of every derivative. No new topology is defined.

## Statements (exact; checked against the file)

1. `iteratedFDeriv_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (n : ℕ) (r : ℝ) (v : ℂ) :
   iteratedFDeriv ℝ n (fun w : ℂ => Real.circleAverage φ w r) v = Real.circleAverage (iteratedFDeriv ℝ n φ) v r`
   (line 137).
2. `tendstoUniformly_iteratedFDeriv_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (n : ℕ) :
   TendstoUniformly (fun r : ℝ => iteratedFDeriv ℝ n (fun v : ℂ => Real.circleAverage φ v r))
   (iteratedFDeriv ℝ n φ) (nhdsWithin (0 : ℝ) (Ioi 0))` (line 146). The codomain is
   `ContinuousMultilinearMap ℝ (fun _ : Fin n => ℂ) ℝ` with its operator norm; uniformity is over all `w ∈ ℂ`.
3. `exists_isCompact_smooth_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
   ∃ K : Set ℂ, IsCompact K ∧ tsupport φ ⊆ K ∧ (∀ r : ℝ, 0 < r → r ≤ 1 → tsupport (fun v => Real.circleAverage φ v r) ⊆ K)
   ∧ ∀ n : ℕ, TendstoUniformly ...` (line 175). Witness `K := testEnlargement φ` (`CircleTestFubiniLimit.lean:43`).

Hypotheses: only `hφ : IsTestFunction univ φ` (`HarmonicBalls/Defs/Laplacian.lean:47`: smooth, compact support, support
in `univ`). No differentiation-under-the-integral, uniform-continuity, probabilistic or Fourier premise is assumed; the
first two are derived.

## Route (as built)

- `norm_circleAverage_le_of_forall` (line 39): pointwise bound on the circle gives `‖circleAverage H w r‖ ≤ M`
  (`intervalIntegral.norm_integral_le_of_norm_le_const`, Mathlib `IntervalIntegral/Basic.lean:771`).
- `norm_circleAverage_sub_le` (line 53): oscillation bound gives `‖circleAverage G w r − G w‖ ≤ M`
  (`Real.circleAverage_fun_sub`, `Real.circleAverage_const`).
- `hasFDerivAt_circleAverage` (line 65): one-step derivative by differentiation under the integral, from the proved
  `HarmonicBalls.hasFDerivAt_translate_integral` (`RouteACircleSmooth.lean:21`) with `g θ = circleMap 0 r θ`.
- `fderiv_circleAverage_eq` (line 83) and `circleAverage_comp_linearIsometryEquiv` (line 90, wraps
  `ContinuousLinearMap.circleAverage_comp_comm`, Mathlib `CircleAverage.lean:324`).
- `iteratedFDeriv_circleAverage_aux` (line 100): induction on `n`, quantified over every complete real normed target
  (the step differentiates the operator-valued `fderiv g`). Uses `iteratedFDeriv_zero_eq_comp` and
  `iteratedFDeriv_succ_eq_comp_right` (Mathlib `FTaylorSeries.lean:819`, `:927`).
- Uniform convergence (line 146): `HasCompactSupport.iteratedFDeriv` and uniform continuity of
  `iteratedFDeriv ℝ n φ`; for `0 < r < δ` every point `circleMap w r θ` lies within `δ` of `w`, so the oscillation is
  at most `ε/2` for every `w` at once.
- Export (line 175): `fixed_enlargement_circleAverage` (`CircleTestFubiniLimit.lean:150`) gives compactness and the
  support bound for `0 < r ≤ 1`; `tsupport φ ⊆ testEnlargement φ` because `0 ∈ closedBall 0 1`.

Quantifier order: each `n` has its own uniform-continuity modulus; the radius limit `𝓝[>] 0` is taken after `n` is
fixed, and the export quantifies `∀ n` only after the fixed compact set `K`.

## Checks

- `lc` on the new module: CHECK OK, log `/home/nitro/paper-fleets/hb/logs/lc/224019-3400761.log`. One earlier error was
  fixed: the helper needed `[CompleteSpace Y]` (target), which Mathlib `circleAverage_comp_comm` requires.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageSmoothTestConvergence`: BUILD OK, log
  `/home/nitro/paper-fleets/hb/logs/lb/224038-3401569.log`.
- Raw scan of the file for `sorry|admit|axiom|native_decide|maxHeartbeats|set_option|unsafe|implemented_by|extern|
  Bonanno|LatticeProb`: 0 hits. No comment contains these tokens, so the raw and comment-aware scans agree.
- Printed axioms (scratch file in `/tmp`, not committed): `iteratedFDeriv_circleAverage`,
  `tendstoUniformly_iteratedFDeriv_circleAverage`, `exists_isCompact_smooth_circleAverage` and
  `iteratedFDeriv_circleAverage_aux` each depend on `[propext, Classical.choice, Quot.sound]` only.
- Credit (Leonardo Bonanno, pinned Lattice-Probability port): not required. Import-closure evidence: a breadth-first walk
  of the `import` lines from the module reaches 14 `HarmonicBalls` modules; every other import is Mathlib. No
  `LatticeProb`, `MarkovProcess` or `EllipticRegularity` module is in the closure, so the file uses no Bonanno code.

## Scope limits (not claimed)

- No summability, Sobolev or Fourier reconstruction, insertion compatibility (r10:1363–1365), distribution-valued `R`,
  or common raw-test representation. These are the consumers and stay separate.
- No new test-function topology, carrier, or provisional definition. No metric moment, physical exponent, literature
  input, or numbered closure.

## Findings

- No gap in the written argument at r10:1046–1062 or 1353–1378: the proved criterion (fixed compact support plus uniform
  convergence of every derivative) is what the text uses. The text does not fix a topology, so the Lean statement is a
  sufficient criterion for convergence in the smooth test topology, not a definition of it.

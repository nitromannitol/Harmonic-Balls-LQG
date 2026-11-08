# Audit: CircleTestIntegralL2Limit (task sec11-circle-test-integral-L2-limit)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleTestIntegralL2Limit.lean` (new), namespaces
`HarmonicBalls.CircleTestIntegralL2Limit` (auxiliary lemmas) and `HarmonicBalls.IsWholePlaneGFF` (main results).
Not imported by `HarmonicBalls.lean` (root file read-only for this task; the operator decides whether to add it).

## Source

Fleet paths (not repository paths):
- `notes/sec11-proof/sec11-proof-r10.tex` lines 1046–1062, in particular 1055–1062: the Gaussian covariance identity and
  `φ * σ_r → φ` with a common compact support. This module formalizes the analytic `L²` part of that argument.
- `notes/sec11-proof/AUDIT-r9.md:17` (table row Round9 TeX 999–1025), retained by `AUDIT-r10.md:110`.

## Statements (exact; checked against the file)

Hypotheses of every main result: `hgff : IsWholePlaneGFF P hC hcirc` (`HarmonicBalls/Defs/GFF.lean:93`) and
`hφ : IsTestFunction Set.univ φ` (`HarmonicBalls/Defs/Laplacian.lean:47`). Nothing else. The carrier is the actual
probability space `(Ω, P)` with `P` a probability measure (`IsWholePlaneGFF.isProbabilityMeasure`), and the spatial
integrals are Lebesgue integrals over `ℂ` (`volume`).

1. `IsWholePlaneGFF.integral_sq_sub_pairing (hgff) {ψ φ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ)
   (hφ : IsTestFunction Set.univ φ) :
   ∫ ω, (hC ω ψ - hC ω φ) ^ 2 ∂P = wholePlaneGFFCov (GFFObservable.pairing fun x => ψ x - φ x)
     (GFFObservable.pairing fun x => ψ x - φ x)`.
   This is the fixed two-test covariance formula. The right-hand side is `∫ x, (ψ x - φ x) * kernelPairing (ψ - φ) x`
   (definitional unfolding of `wholePlaneGFFCov`/`smear`).
2. `IsWholePlaneGFF.memLp_circleTestIntegral_sub (hgff) {φ : ℂ → ℝ} (hφ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
   MemLp (fun ω => (∫ w, hcirc ω r w * φ w) - hC ω φ) 2 P`.
3. `IsWholePlaneGFF.tendsto_integral_sq_circleTestIntegral_sub (hgff) {φ} (hφ) :
   Tendsto (fun r : ℝ => ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P) (𝓝[>] 0) (𝓝 0)`.
   (`𝓝[>] 0` is `nhdsWithin 0 (Set.Ioi 0)`.)
4. `IsWholePlaneGFF.tendsto_integral_sq_circleTestIntegral_sub_dyadicScale (hgff) {φ} (hφ) :
   Tendsto (fun n : ℕ => ∫ ω, ((∫ w, hcirc ω (dyadicScale n) w * φ w) - hC ω φ) ^ 2 ∂P) atTop (𝓝 0)`
   (`dyadicScale` at `HarmonicBalls/Defs/LQG.lean:41`).

Auxiliary lemmas (namespace `HarmonicBalls.CircleTestIntegralL2Limit`): `exists_ball_of_test` (a test function
vanishes outside a ball), `measurable_wholePlaneCov_right`, `integrableOn_abs_wholePlaneCov_ball`,
`integral_abs_wholePlaneCov_ball_le`, `abs_kernelPairing_le`, `stronglyMeasurable_kernelPairing`,
`integrable_mul_wholePlaneCov`, `integrable_mul_kernelPairing`, `kernelPairing_sub`, `isTestFunction_univ_sub`,
`exists_radius_sup_circleAverage_sub`, `exists_ball_circleAverage_sub_eq_zero`, `integral_sq_le_of_bound`,
`tendsto_integral_sq_circleAverage_sub`. All are unconditional (no hypotheses beyond the stated test-function ones).

## Route (as built)

- Circle averages to pairings: `IsWholePlaneGFF.ae_integral_circle_mul_eq_pairing_circleAverage`
  (`Proofs/Sec11/ClosureScales/GaussianCircleTestIntegral.lean`, commit facb52b) gives, for `0 < r ≤ 1`, a.s.
  `∫ w, hcirc ω r w * φ w = hC ω (circleAverage φ · r)`. Then `MemLp.ae_eq` transfers `memLp_pairing` to the claim 2.
- Covariance expansion (claim 1): `(X - Y)² = X·X - 2 X·Y + Y·Y` for `X = hC ψ`, `Y = hC φ`, integrable by
  `MemLp.integrable_mul`. Each product mean is a covariance (`covariance_eq_integral_mul` and `covariance_eq`), so
  `E[X·Y] = ∫ ψ · kernelPairing φ` and the symmetry `E[Y·X] = E[X·Y]` comes from commutativity, not from Fubini.
  `integral_pairing_mul_pairing` (`E[X²] = ∫ ψ · kernelPairing ψ`) is reused. Kernel side: `kernelPairing_sub`
  (pointwise linearity in the test function, from integrability of `y ↦ b y * wholePlaneCov x y`) and
  `integrable_mul_kernelPairing` (integrability of `x ↦ a x * kernelPairing b x`, by a uniform bound
  `abs_kernelPairing_le` on balls via `kernelBoxConst`) justify splitting the integrals. No samplewise linearity of
  `hC` is used and `hC(ψ - φ) = hC ψ - hC φ` is never asserted.
- Schur bound (claims 2, 3): `abs_wholePlaneGFFCov_pairing_le` (`Proofs/Sec11/ClosureScales/RouteAKernelBox.lean`)
  gives `|wholePlaneGFFCov (pairing f) (pairing f)| ≤ (2 kernelBoxConst M).toReal · ∫ f²` for `f` supported in
  `ball 0 M` and bounded. Here `f = circleAverage φ · r - φ` is a test function (`isTestFunction_univ_sub`).
- Support: `exists_isCompact_smooth_circleAverage` (CircleAverageSmoothTestConvergence, commit b80b997) gives a
  compact `K` containing `tsupport φ` and every `tsupport (circleAverage φ · r)` for `0 < r ≤ 1`; `K ⊆ closedBall 0 R`
  gives `M = R + 1` (`exists_ball_circleAverage_sub_eq_zero`).
- Uniform convergence: `norm_circleAverage_sub_le` with uniform continuity of the compactly supported `φ`
  (`exists_radius_sup_circleAverage_sub`). This is equivalent to the `n = 0` case of
  `tendstoUniformly_iteratedFDeriv_circleAverage` (b80b997), which is not used.
- `∫ f² ≤ δ² · vol(ball 0 M)` (`integral_sq_le_of_bound`) plus the squeeze gives `∫ (φ_r - φ)² → 0` within `𝓝[>] 0`;
  `squeeze_zero_norm'` with the Schur bound gives claim 3; `dyadicScale` tends to `0` within `𝓝[>] 0`
  (`tendsto_dyadicScale_nhdsGT`, `HarmonicBalls/Proofs/Sec8/OpenBallDensity.lean:78`) gives claim 4.

## Kernel convention

`wholePlaneCov z w = log (max ‖z‖ 1 * max ‖w‖ 1 / ‖z - w‖)` (`Defs/GFF.lean`). On the diagonal Lean's `log (·/0) = 0`
junk value is used; the diagonal is Lebesgue-null, so the integrals are unaffected. All integrals against
`kernelPairing` are over test functions, for which integrability is proved above.

## Import closure and credit

Closure of the module's `import` graph: 23 `HarmonicBalls` files (this module included) plus Mathlib; no `LatticeProb`, `MarkovProcess` or
`EllipticRegularity` module (checked by a BFS over the `import` lines). The module uses no Lattice-Probability code, so
no Leonardo Bonanno credit line is required.

## Checks

- `lc` (lock-free check, warnings as errors): CHECK OK.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestIntegralL2Limit`: BUILD OK.
- Raw scan (`sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats`, `unsafe`, `implemented_by`, `extern`,
  comments included): 0 hits. No `set_option maxHeartbeats` line in the file.
- `#print axioms` (scratch file in `/tmp`, not committed) for the four main declarations:
  `[propext, Classical.choice, Quot.sound]` each.

## Not proved here (remaining consumers)

- The source's full dyadic almost-sure limit on the canonical distribution model.
- Distribution-valued `R`, the `H^{-2}` reconstruction, and the simultaneous raw-test representation.
  `L²(P)` convergence alone does not supply them.
- Remaining written consumers, unchanged: `sec11-proof-r10.tex:1060` (reconstruction limit) and
  `sec11-proof-r10.tex:1363-1365` (insertion compatibility).
- Untouched: `RawToProfileStep`, the E56 carrier and coded-Palm operator ruling, the existing DMS `hU` review, and every
  frozen Draft, External, Proposed, paper, dependency or root-import file.
- No literature input, physical exponent, metric moment, Pfeffer Def 1.6 membership or Prop 4.6, and no numbered closure
  is claimed.

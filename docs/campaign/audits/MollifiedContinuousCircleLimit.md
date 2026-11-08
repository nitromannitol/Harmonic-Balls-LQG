# Audit: MollifiedContinuousCircleLimit (task sec11-mollified-continuous-circle-limit)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/MollifiedContinuousCircleLimit.lean` (new).
Source: r10 `l:r9-circle-code1323-1330`, `notes/sec11-proof/sec11-proof-r10.tex` lines 1323-1330, with the
independent audits AUDIT-r9.md and AUDIT-r10.md. The printed argument uses uniform continuity of `u` on a compact
enlargement of the circle; the proof realizes that step by the parametric interval-integral continuity theorem
(the route fixed by the task), which needs only continuity of `u`.
Imports: `MollifiedLogCircleLimit` (commit d95497e) and Mathlib. No External or Proposed input, no new hypothesis,
no random field, decoder or E56 object. The import closure of `MollifiedLogCircleLimit` is 12 repository modules and
contains no Lattice-Probability module, so no Leonardo Bonanno credit line is required.

## Statement (namespace `HarmonicBalls`)

- `mollified_continuous_circle_limit {rho : ℂ → ℝ} (_h_even : ∀ x, rho (-x) = rho x) (h0 : ∀ x, 0 ≤ rho x)
  (h_smooth : ContDiff ℝ ∞ rho) (h_supp : tsupport rho ⊆ closedBall 0 1) (hint : ∫ x, rho x = 1) {u} (hu : Continuous u)
  {r} (hr : 0 < r) (w : ℂ)`: the conjunction of
  (i) `∀ e, 0 < e → Integrable (fun v => u v * Real.circleAverage (fun x => (e ^ 2) ^ (-1 : ℤ) * rho ((e ^ (-1 : ℤ)) • (x - v))) w r)`;
  (ii) `Tendsto (fun e => ∫ v, u v * Real.circleAverage (same kernel) w r) (𝓝[>] 0) (𝓝 (Real.circleAverage u w r))`.
  The kernel is the literal formula of r10 (`(e^2)^(-1)`, `e^(-1) • ·`, with integer exponents). No boundedness,
  compact support, differentiability or integrability is assumed on `u`; the statement is universal in `u`.
- Auxiliary declarations: `kernel_eq_mollifierAt` (literal kernel = `mollifierAt rho e x`, by `zpow_neg_one`);
  `circleAverage_kernel_eq` (shift of the literal kernel = circle average of `mollifierAt rho e (· - v)`);
  `continuous_circleAverage_center` (centre continuity of the circle average of a continuous `u`);
  `integrable_mul_circleAverage_kernel` (part (i)); `tendsto_mul_circleAverage_kernel` (part (ii)).

## Proof route

- (i): rewrite the kernel as `mollifierAt rho e (· - v)`. `continuous_circleAverage_mollifierAt` gives continuity in `v`,
  `circleAverage_mollifierAt_eq_zero` gives vanishing outside `closedBall w (r + e)` (for `e > 0`), and
  `integrable_mul_of_zero_outside` applies with `u.locallyIntegrable` and `u.measurable`.
- (ii): `integral_mul_circleAverage_mollifierAt` (Fubini, using `h_supp`, `hc`, `hu.measurable`, `hu.locallyIntegrable`)
  rewrites the integral as `∫ y, mollifierAt rho e y * circleAverage (fun x => u (x - y)) w r`. `circleAverage_comp_sub`
  turns the inner average into `circleAverage u (w - y) r`. This map is continuous: `continuous_circleAverage_center`
  composed with `y ↦ w - y`. `tendsto_integral_mollifierAt_mul` (approximate identity for a continuous `h`, no global
  bound) gives the limit `circleAverage u (w - 0) r = circleAverage u w r` along `𝓝[>] 0`. `Tendsto.congr'` with the
  eventual equality on `Ioi 0` (`self_mem_nhdsWithin`) transports it to the literal integrals.
- Used from the proof: continuity of `rho` (from `h_smooth`), nonnegativity, the support condition and `∫ rho = 1`.
  `_h_even` is not used (carried to match the statement).

## Reuse search

- `MollifiedLogCircleLimit.lean`: `mollifierAt` (line 36), `tendsto_integral_mollifierAt_mul` (85),
  `circleAverage_comp_sub` (142), `continuous_circleAverage_mollifierAt` (170), `circleAverage_mollifierAt_eq_zero` (200),
  `integrable_mul_of_zero_outside` (216), `integral_mul_circleAverage_mollifierAt` (255). All reused unchanged.
- Mathlib `Continuous.circleAverage` (`MeasureTheory/Integral/CircleAverage.lean:217`) is continuity in the radius only,
  so it does not give centre continuity. The project's `continuous_circleAverage_radius_center`
  (`Proofs/Sec6/ContinuousWeylCircleAverage.lean:17`) would, but that file imports `Sec8/VagueMassConvergence`; the
  centre continuity is proved locally by the same parametric-integral method, to keep the import closure unchanged.
- `CircleDensityContinuousLimit` concerns the radial annular kernel and is not used.

## Checks

- `lc` on the module: CHECK OK, 0 warnings (lc runs with `-DwarningAsError=true`).
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedContinuousCircleLimit`: BUILD OK.
- Forbidden tokens: raw grep and comment-aware scan for `sorry`, `axiom`, `admit`, `native_decide`,
  `maxHeartbeats`: none.
- `#print axioms` (scratch file outside the repository, importing the module) for all six declarations:
  `[propext, Classical.choice, Quot.sound]`.

## Open items

- None for this statement. The written argument contains no step beyond the reused lemmas, so no gap is reported.
- Consumers: the statement is pointwise in `u`, so it applies to each sample-dependent continuous addition without a
  probability-one intersection. It does not supply the RawToProfile or reconstruction closure, and it does not touch the
  E56 carrier or coded-Palm ruling.

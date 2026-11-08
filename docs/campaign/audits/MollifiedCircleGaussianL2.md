# Audit: MollifiedCircleGaussianL2 (task sec11-mollified-circle-gaussian-l2)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/MollifiedCircleGaussianL2.lean` (new, 568 lines).
Source: r10 `l:r9-circle-code1291-1303`, `notes/sec11-proof/sec11-proof-r10.tex` lines 1287-1303 (the
expansion into two variances and a mixed covariance; potential `log max(r,|x-w|)`; Fubini moves each mollifier onto
the potential; approximate identities; `log max(1,|x|)` continuous).
Imports: `Defs.GFF`, `MollifiedLogCircleLimit`, `MollifiedContinuousCircleLimit`, `RouteACircleSmooth`,
`RootedShiftProfile`, `Potential.Fundamental`, and Mathlib. No External or Proposed input, no new literature premise,
no convergence, covariance-limit, decoder, representation or E56 hypothesis.

## Hypotheses

- `IsLiteralMollifier rho` (structure, lines 43-48): the five conditions of the r10 statement: even, nonnegative,
  `ContDiff ℝ ∞ rho`, `tsupport rho ⊆ closedBall 0 1`, `∫ rho = 1`. Nothing else.
- Fixed circle: `w : ℂ`, `{r : ℝ} (hr : 0 < r)`. The random field: `IsWholePlaneGFF P hC hcirc` (Defs/GFF.lean:93),
  with `[MeasurableSpace Ω] {P : Measure Ω}` and no further assumption.

## Declarations

- `circleMollifier rho w r e v` (line 51): the literal kernel `Real.circleAverage (fun x => (e^2)^(-1:ℤ) * rho ((e^(-1:ℤ)) • (x - v))) w r`, i.e. `phi_e`.
- `isTestFunction_circleMollifier` (line 78): `IsTestFunction univ (circleMollifier rho w r e)` for `0 < e`.
  Smoothness via `HarmonicBalls.contDiff_circleAverage_of_contDiff` after `circleAverage_comp_sub`; compact support via
  `circleAverage_mollifierAt_eq_zero`.
- `tendsto_integral_circleMollifier_mul` (line 95): for continuous `u`, `∫ u * phi_e → Real.circleAverage u w r` on `𝓝[>] 0`
  (from `mollified_continuous_circle_limit`). `tendsto_integral_circleMollifier` (line 101): the mass `→ 1`.
- Potential (lines 108-157): `circlePot w r p = log max(r, |p - w|)`; `abs_circlePot_sub_le`: `|P p - P q| ≤ |p - q| / r`;
  `continuous_circlePot`; `circleIntegrable_log_norm_x_sub` (Mathlib's `circleIntegrable_log_norm_sub_const`).
- Log insertion (lines 161-270): `integral_circleMollifier_mul_log_norm_sub` (line 161): `∫ phi_e(y) log|x-y| dy = ∫ mollifierAt(y) P(y+x) dy`
  (Fubini via `integral_mul_circleAverage_mollifierAt` and `circleAverage_log_sub`); `abs_mollifiedPot_sub_circlePot_le`
  (line 195): `|J_e x - P x| ≤ e / r`; `abs_mollifiedPot_sub_mollifiedPot_le` (line 222): `J_e` is `1/r`-Lipschitz;
  `continuous_mollifiedPot` (line 247).
- Kernel (lines 274-330): `wholePlaneCov_eq_of_ne` (off the diagonal `wholePlaneCov x y = L x + L y - log|x-y|`);
  `circleAverage_wholePlaneCov` (line 282): the circle average of the kernel in the second variable is
  `circleKernelMean w r x = L x + c - P x`. The diagonal is handled by `circleAverage_congr_codiscreteWithin` with
  `compl_singleton_mem_codiscreteWithin`, so no measure-zero hypothesis is needed.
  `wholePlaneGFFCov_circle_circle_eq` (line 309) and `circleAverage_circleKernelMean` (line 316): `Phi' = 2c - avg P`.
- Limits (lines 332-482): `integral_circleMollifier_mul_wholePlaneCov` (line 334), `wholePlaneGFFCov_pairing_pairing_eq`
  (line 364): `Phi_e = 2 m_e A_e - B_e`; `tendsto_integral_circleMollifier_mul_mollifiedPot` (line 400): `B_e → avg P`;
  **`tendsto_wholePlaneGFFCov_pairing_pairing` (line 450)**: `wholePlaneGFFCov (pairing phi_e) (pairing phi_e) → wholePlaneGFFCov (circle r w) (circle r w)`;
  **`tendsto_wholePlaneGFFCov_pairing_circle` (line 469)**: `wholePlaneGFFCov (pairing phi_e) (circle r w) → wholePlaneGFFCov (circle r w) (circle r w)`.
- Gaussian (lines 484-566): `integral_sq_sub_eq_covariance` (line 486): `∫ (X - Y)^2 = cov X X - 2 cov X Y + cov Y Y` for centred `L²` variables;
  **`isWholePlaneGFF_circleMollifier_L2` (line 520)**: for `0 < e`, `MemLp (fun ω => hC ω phi_e - hcirc ω r w) 2 P`, and
  `Tendsto (fun e => ∫ ω, (hC ω phi_e - hcirc ω r w)^2 ∂P) (𝓝[>] 0) (𝓝 0)`.

## Route notes (fidelity)

- The printed "uniform convergence of approximate identities on a compact enlargement" is realized by the Lipschitz bound
  `|P p - P q| ≤ |p - q| / r`, which gives `|J_e x - P x| ≤ e / r` for all `x` (no compactness needed). This proves the
  claimed convergence; it is not a new claim.
- "Fubini moves each mollifier onto the potential" is `integral_mul_circleAverage_mollifierAt` followed by
  `circleAverage_log_sub` (Mathlib mean value identity `circleAverage_log_norm_sub_eq_log_max`).
- The kernel uses the Lean junk value `log 0 = 0` on the diagonal (`Defs/GFF.lean`). It is only seen by the circle
  average in the second variable, where a single point is codiscrete (handled above); the Lebesgue integral in the first
  variable is insensitive to it.
- Gaussian part: `MemLp` from `hasGaussianLaw_eval(...).memLp_two` and `hasGaussianLaw_circle(...).memLp_two`;
  covariances from `covariance_eq`; means from `integral_eq_zero`. The Gaussian theorem does not use
  `tendstoInMeasure_circleDensity_pairing` (a different annular kernel).

## Checks

- `lc`: CHECK OK, 0 errors, 0 warnings. `lb`: BUILD OK (`HarmonicBalls.Proofs.Sec11.ClosureScales.MollifiedCircleGaussianL2`).
- Raw scan (`sorry|axiom|admit|native_decide|maxHeartbeats`): none. Comment-aware scan (block and line comments removed): none.
- `#print axioms` on all 29 declarations of the module: `propext`, `Classical.choice`, `Quot.sound` only (scratch file
  `/tmp/z3-axcheck/AxCheck.lean`, outside the repository).
- Import closure: 15 repository modules, none a Lattice-Probability module. `MollifiedContinuousCircleLimit.lean` says
  explicitly that no Lattice-Probability declaration is used. So no Leonardo Bonanno credit line is required.
- Lean note: `ω` is an active scoped notation token (`OrderType.omega0`) in this import context, so the binder names in
  this file are `ξ` where Mathlib's `∫ ω, …` would be used.

## Open items

None for this statement. Not touched: `RawToProfileStep`, `CanonicalProfile`, E56, frozen Defs/Draft, External/Proposed,
paper files, other workers' files.

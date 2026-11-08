# Audit: FixedSquareFrontierNull (zero-charge LQG, Lebesgue-null sets, fixed square frontier)

Task: `zero-charge-lqg-fixed-square-frontier-null` (worker z3, round 1).
Module: `HarmonicBalls/Proofs/Sec11/FixedSquareFrontierNull.lean` (new, outside `Closure/`).

## Status

- `lc`: CHECK OK. `lb HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull`: BUILD OK, 0 errors.
- Forbidden-token scan of the module (`sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`, `Proposed`,
  `External`): 0 hits. No `set_option` in the module.
- `#print axioms` (check file outside the repository, compiled with `lc`) for the two main results and four helpers:
  `[propext, Classical.choice, Quot.sound]` only.

## Declarations (namespace `HarmonicBalls`)

- `IsWholePlaneGFF.ae_lqgMeasure_eq_zero_of_isCompact_volume_eq_zero` (main). Inputs: `hgff : IsWholePlaneGFF P hC hcirc`,
  `_hγ : 0 < γ`, `_hγ2 : γ < 2` (paper scope; not used by the proof, the bound holds for all real `γ`),
  `hμ : IsLQGMeasureOfField P γ 0 hcirc μ` (zero charge, `α₀ = 0`), `hK : IsCompact K`, `hKv : volume K = 0`.
  Conclusion: `∀ᵐ ω ∂P, μ ω K = 0`. `K` is fixed before `ω`.
- `IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero`. Same hypotheses with `(a : ℂ) {L : ℝ} (hL : 0 ≤ L)`.
  Conclusion: `∀ᵐ ω ∂P, μ ω (frontier (closedSquare a L)) = 0`. The square is deterministic; this is not
  `SquareContinuitySelection` (which chooses good squares).
- Helpers: `fieldCircleAverage_zero_charge`, `circleAverage_wholePlaneNormalization_le`,
  `IsWholePlaneGFF.variance_circleAverage_eq`, `IsWholePlaneGFF.lintegral_exp_circleAverage_eq`,
  `IsWholePlaneGFF.lintegral_density_le`, `lintegral_eq_liminf_of_tendsto`, `exists_cutoff_of_isCompact`,
  `IsWholePlaneGFF.lintegral_lqgMeasure_le_of_cutoff`, `volume_setOf_re_eq_const`, `volume_setOf_im_eq_const`.

## Route (first moment, then Urysohn cutoffs)

1. Variance of circle averages. `Var h_r(z) = 2 A_r(z) - log r`, where `A_r(z)` is the circle average of
   `wholePlaneNormalization = log (max |·| 1)` over `∂B_r(z)`. From `wholePlaneGFFCov_concentric_circles_general`
   and `covariance_eq` (the GFF covariance `wholePlaneCov`). For `0 < r ≤ 1` and `‖z‖ ≤ R`: `A_r(z) ≤ log (R + 1)`.
2. Gaussian exponential moment. `E exp(γ h_r(z)) = exp(γ² Var h_r(z) / 2)` (law of the circle average is
   `gaussianReal 0 Var`, Mathlib `mgf_id_gaussianReal`).
3. Dyadic density bound. `E[ε^{γ²/2} exp(γ h_ε(z))] ≤ (R + 1)^{γ²}` for `0 < ε ≤ 1`, `‖z‖ ≤ R`: the `ε` powers cancel
   exactly against `-log ε` in the variance bound.
4. Tonelli on `P ⊗ Leb` for the jointly measurable version `H` of `exists_jointlyMeasurable_circleAverage`, which equals
   `hcirc` almost surely for all `(r, z)`; then Fatou on the dyadic approximations, with the a.s. vague convergence of
   `IsLQGLimit` (the Bochner limit of `lqgApprox`). Identity `∫⁻ f dm = liminf ∫⁻ f dν_k` is proved in
   `lintegral_eq_liminf_of_tendsto` (integrability of `f` for each approximation from finiteness of the lintegral).
   Result: `E μ(K) ≤ (R + 1)^{γ²} ∫⁻ f dLeb` for every continuous `0 ≤ f ≤ 1` with `f = 1` on `K` and `f = 0` off `B_R`.
5. Urysohn cutoffs of `cthickening δ K` (`exists_cutoff_of_isCompact`), `δ ↓ 0`, and `Leb (cthickening δ K) → Leb K = 0`
   give `E μ(K) = 0`, hence `μ(K) = 0` a.s. (`lintegral_eq_zero_iff'`).
6. Square. The frontier of `closedSquare a L` is closed in the compact `closedSquare a L`, hence compact; it lies on
   four lines (`frontier_closedSquare_subset_lines`), each Lebesgue-null.

No samplewise absolute-continuity `μ ω ≪ volume` is assumed or derived. No new literature input, no staged Prop, no
frozen definition or `Draft` statement changed.

## Reused proved APIs (no new inputs)

- `IsWholePlaneGFF.exists_jointlyMeasurable_circleAverage`, `IsWholePlaneGFF.aemeasurable_lqgApprox`
  (`HarmonicBalls/Proofs/Sec5/CircleAverageMeasurability.lean`).
- `IsWholePlaneGFF.hasGaussianLaw_circle`, `covariance_eq`, `integral_eq_zero` (`HarmonicBalls/Defs/GFF.lean`).
- `wholePlaneGFFCov_concentric_circles_general` (`HarmonicBalls/Proofs/Sec8/ConcentricCircleCovariance.lean`).
- `wholePlaneNormalization`, `continuous_wholePlaneNormalization` (`HarmonicBalls/Proofs/Sec8/CircleLogPotential.lean`).
- `IsWholePlaneGFF.aemeasurable_lqgMeasure` (`HarmonicBalls/Proofs/Sec5/OpenMeasureLaw.lean`).
- `dyadicScale_pos`, `lqgApprox`, `IsLQGLimit`, `IsLQGMeasureOfField` (`HarmonicBalls/Defs/LQG.lean`).
- `frontier_closedSquare_subset_lines` (`HarmonicBalls/Proofs/Sec11/SquareFrontierLines.lean`), `closedSquare` (`HarmonicBalls/Defs/LBM.lean`).
- Mathlib: `integrable_exp_mul_gaussianReal`, `mgf_id_gaussianReal`, `lintegral_lintegral_swap`,
  `tendsto_measure_cthickening_of_isCompact`, `exists_continuous_zero_one_of_isCompact`,
  `Complex.volume_preserving_equiv_real_prod`, `Real.circleAverage_mono`, `Real.circleAverage_const`.

## Import closure and credit (Leonardo Bonanno)

- The import closure of the module has 225 `HarmonicBalls` files. It reaches the external LatticeProb module
  `LatticeProb.Prob.Birkhoff` through `HarmonicBalls/Proofs/Sec8/BirkhoffPort.lean`, which credits Leonardo Bonanno.
  The module docstring carries the same credit as `Proofs/Sec11/ClosureMeasureMeasurable.lean`.
- The closure also contains `HarmonicBalls/Proposed/Birkhoff.lean` (it imports `LatticeProb.Prob.Birkhoff`), and
  MarkovProcess modules (Brownian motion, external package). These are reached through existing imports only. No Prop of
  `Proposed/` or `External/` is used as a hypothesis by the two main results (their hypotheses are the GFF structure, the
  LQG measure hypothesis, the compact set, and `0 < γ < 2`). The operator should note that the Proposed module is in the
  closure of any module that imports `Proofs/Sec8/BirkhoffPort.lean`.
- The closure check was run by a bash import walk on the sandbox (HarmonicBalls imports only).

## Open points and gaps

- None for the stated scope. `0 < γ < 2` is kept in the statement and is unused; the first-moment bound holds for all real
  `γ`. The paper's scope is therefore preserved, not strengthened.
- The square result is for `frontier (closedSquare a L)` with `L ≥ 0`. A square with `L < 0` is not in the paper's use.

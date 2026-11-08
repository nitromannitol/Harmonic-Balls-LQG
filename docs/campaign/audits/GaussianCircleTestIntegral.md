# Audit: GaussianCircleTestIntegral (task sec11-gaussian-circle-test-integral-identity)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/GaussianCircleTestIntegral.lean` (new, 640 lines).
Source: the written reconstruction step, `notes/sec11-proof/sec11-proof-r10.tex` lines 1046-1062 (fleet path): the
identity `∫ c(r,z) φ(z) dz = (g, φ * σ_r)` holds first in `L²` from the joint Gaussian covariance, then almost surely
for a countable family of tests and radii. No gap was found in that argument; the Lean proof supplies the Fubini
justifications that the written text leaves implicit.

## Statements (exact)

- `IsWholePlaneGFF.ae_integral_circle_mul_eq_pairing_circleAverage` (line 507). Arbitrary `Ω`, `[MeasurableSpace Ω]`,
  `P`, `hC`, `hcirc`, `hgff : IsWholePlaneGFF P hC hcirc`, `hphi : IsTestFunction Set.univ φ`, `0 < r`, `r ≤ 1`:
  `∀ᵐ ω ∂P, Integrable (fun w => hcirc ω r w * φ w) ∧ ∫ w, hcirc ω r w * φ w = hC ω (fun v => Real.circleAverage φ v r)`.
  The averaged test `v ↦ Real.circleAverage φ v r` is proved to be a test function inside the proof
  (`CircleTestFubini.isTestFunction_univ_circleAverage`, `CircleTestFubiniLimit.lean:142`).
- `IsWholePlaneGFF.exists_measurable_conull_ae_integral_circle_mul_eq_pairing_circleAverage` (line 619). Arbitrary
  countable `ι`, `κ`; tests `φ : ι → ℂ → ℝ` with `IsTestFunction univ`, radii `r : κ → ℝ` with `0 < r k ≤ 1`, all fixed
  before `ω`. Conclusion: `∃ S, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ω ∈ S, ∀ i k, (the single-test statement)`. Proof:
  `ae_all_iff` over `ι` and `κ`, then `exists_measurable_superset_of_null` on the exceptional set.

## Inputs (no new premise)

- Only the fields of `IsWholePlaneGFF` (`Defs/GFF.lean`): `measurable_pairing` (line 96), `measurable_circle` (98),
  `isGaussianProcess` (100), `integral_eq_zero` (103), `covariance_eq` (105), `ae_continuousOn_circle` (108).
- Hypothesis-free use of the sample: `hC ω` is never assumed linear in `φ` and no raw representation of `hC` is used.
  All identities pass through the fixed-test Gaussian laws.
- No `External` or `Proposed` input. No `sorry`, `admit`, `axiom`, `native_decide`, and no heartbeat override
  (raw scan of the file: 0 hits).

## Covariance scopes (exact)

- `covariance_eq` (`GFF.lean:105`) fixes `cov[o.eval, o'.eval; P] = wholePlaneGFFCov o o'` for **every** pair of
  admissible observables (no a.e. qualifier). Used as:
  - `integral_circle_mul_circle` (line 455): `∫ hcirc ω r w * hcirc ω r w' = circleCovKernel r w w'` for every
    `w, w' ∈ ℂ` (`circleCovKernel r w w' = Real.circleAverage (circleKernelMean w' r) w r`, line 94, equal to
    `wholePlaneGFFCov (circle r w) (circle r w')` by `circleAverage_wholePlaneCov`, `MollifiedCircleGaussianL2.lean:282`).
  - `integral_circle_mul_pairing` (line 470): `∫ hcirc ω r w * hC ω ψ = Real.circleAverage (kernelPairing ψ) w r`,
    `kernelPairing ψ x = ∫ y, ψ y * wholePlaneCov x y` (line 114).
  - `integral_pairing_mul_pairing` (line 485): `∫ hC ω ψ * hC ω ψ = ∫ x, ψ x * kernelPairing ψ x`.
- Passage from covariance to expectation (`covariance_eq_integral_mul`, line 435): exact, since the means vanish by
  `integral_eq_zero` (line 103); no integrability is needed for that identity.
- Square integrability comes from the Gaussian law: `memLp_circle` (line 443; `hasGaussianLaw_circle`, `GFF.lean:190`)
  and `memLp_pairing` (line 449).

## Null-set scopes (exact)

- Measurable version: `exists_measurable_circleAverage_version` (`CircleAverageJointMeasurable.lean:22`) gives `g`
  with `Measurable (uncurry g)`, `∀ ω, Continuous (g ω)`, and a measurable `N`, `P N = 0`, such that
  `∀ ω ∉ N, ∀ z, g ω z = hcirc ω r z` (the null set does not depend on `z`). Used in the proof with
  `filter_upwards [hae]`, `hae : ∀ᵐ ω, ω ∉ N`.
- Single-test exceptional set: `N ∪ {ω | (∫ g ω w φ w) ≠ hC ω φ_r}`, which is null because the second moment of the
  difference vanishes (`integral_eq_zero_iff_of_nonneg`, and `hsum` in the main proof). Hence the single-test
  statement holds only **almost surely**, as required.
- Countable corollary: one measurable conull set `S = (measurable superset of ⋃ exceptional sets)ᶜ`.

## Deterministic core (no probability)

- `integral_circleKernelMean_mul_eq_kernelPairing` (line 131): `∫ w, circleKernelMean w r x * φ w = kernelPairing φ_r x`
  by circle-average adjointness (`CircleTestFubiniLimit.lean:378`) applied to `y ↦ wholePlaneCov x y`.
- `continuous_kernelPairing` (line 149): `kernelPairing φ_r` is continuous (parametric integral).
- `integral_prod_circleCovKernel` (line 166): `∫∫ φ(w) φ(w') circleCovKernel r w w' = ∫ x, φ_r(x) kernelPairing φ_r(x)`
  (two Fubini swaps on `ℂ × ℂ` for continuous compactly supported integrands and two adjointness steps).
- `abs_wholePlaneCov_le` (line 36): `|wholePlaneCov x y| ≤ logMaxOne x + logMaxOne y + |log ‖x-y‖|`.
- `locallyIntegrable_wholePlaneCov_right` (line 68), from `integrableOn_abs_log_norm_ball` (`RouteAKernel.lean:31`) and
  `locallyIntegrable_comp_sub_of_integrableOn_ball` (`Potential/Fundamental.lean:67`).

## Probability Fubini (all integrability proved, not assumed)

- `integrable_weighted_sq` (line 218): `ω ↦ ∫ |φ(w)| g(ω,w)² dw` is integrable (Tonelli over `lintegral`; the diagonal
  kernel `circleCovKernel r w w` is continuous with compact support against `|φ|`).
- `integral_pairing_mul_eq` (line 274) and `integrable_and_integral_sq_pairing` (line 335): Fubini on `Ω × ℂ` and
  `Ω × (ℂ × ℂ)` via `integrable_prod_of_bound` (`MollifiedLogCircleLimit.lean:231`), with explicit domination.

## Checks

- `lc`: `CHECK OK` (warnings are errors; the file is warning-free).
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.GaussianCircleTestIntegral`: `BUILD OK`, no diagnostics.
- Printed axioms (both main declarations): `[propext, Classical.choice, Quot.sound]`.
- Credit: the import closure is 19 HarmonicBalls modules plus Mathlib, found by a breadth-first scan of the imports; none
  is a LatticeProb, MarkovProcess or EllipticRegularity module, so no Bonanno credit line is required. (An earlier draft
  imported `Sec8/CircleDensityDoubleLog`, which pulled in LatticeProb; that import was unused and removed.)

## Not claimed

- No all-test statement: each test/radius pair is almost sure, and the countable event is the only uniform statement.
- No distribution-valued `R`, no full raw-test representation, no samplewise linearity of `hC`.
- No summability, Sobolev/Fourier reconstruction, `H^{-2}` object, or per-test radius-to-zero convergence (these
  remain separate steps of the reconstruction).
- No metric moment, no Pfeffer class membership, no physical exponent, no literature admission, no numbered closure.

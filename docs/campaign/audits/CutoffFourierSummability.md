# Audit: CutoffFourierSummability (task `sec11-cutoff-fourier-weighted-summability`)

Owner: z3. File: `HarmonicBalls/Proofs/Sec11/ClosureScales/CutoffFourierSummability.lean` (new, 278 lines, namespace `HarmonicBalls`).
Status: `lc` CHECK OK and `lb` BUILD OK (both with `-DwarningAsError=true`); printed axioms of the eight public
declarations are exactly `[propext, Classical.choice, Quot.sound]`; committed with this audit (see `git log`).

## 1. Written source and what the audit rows say

- Written argument: `/home/nitro/paper-fleets/hb/notes/sec11-proof/sec11-proof-r10.tex`, lines 1064-1074 (uniform
  Fourier variance; finite weighted sum; intersect cutoffs). The step: for a fixed compact cutoff `χ`, the second moment
  of each Fourier coefficient of `χ g` is bounded uniformly in the frequency by the integral of
  `|G(x,y)| |χ(x)χ(y)|`; that integral is finite by local integrability of the logarithmic singularity;
  `∑_{k∈ℤ²} (1+|k|²)^(-2) < ∞`; intersect over the cutoffs.
- Audit rows named by the brief, read in this round:
  - `AUDIT-r9.md:17` is the table row "999-1025 | Identify reconstruction of the shifted code | CONFIRMED: Fubini is
    justified on one compact enlargement ...". It concerns the shifted-code reconstruction. It does not state the
    uniform Fourier second-moment bound, so it is not cited here as verification of this step.
  - `AUDIT-r10.md:110` is a retention note on the round-9 G1 finding. It also does not cover this step.
  - The bound below is formalized from the Lean provider `IsWholePlaneGFF.integral_sq_pairing_le` and the written
    argument, not from those rows.

## 2. Declarations (namespace `HarmonicBalls`; the only hypotheses are `IsWholePlaneGFF` and `IsTestFunction`)

| Declaration | Lean statement (summary) | Line |
|---|---|---|
| `cutoffCosTest χ L k` | `fun x => χ x * Real.cos ((2π/L) * (k.1 * x.re + k.2 * x.im))` | 43 |
| `cutoffSinTest χ L k` | the same with `Real.sin` | 47 |
| `contDiff_cutoffPhase L k` | the smooth phase, `ContDiff ℝ (⊤ : ℕ∞)` | 51 |
| `isTestFunction_cutoffCosTest hχ L k` | `IsTestFunction Set.univ (cutoffCosTest χ L k)` | 57 |
| `isTestFunction_cutoffSinTest hχ L k` | the sine analogue | 62 |
| `frequencyWeight_nonneg k` | `0 ≤ (1 + k.1² + k.2²)^(-2 : ℤ)` | 67 |
| `summable_one_add_sq_zpow_neg_one` | `Summable (fun n : ℤ => (1 + n²)^(-1 : ℤ))` | 73 |
| `frequencyWeight_le_prod a b` | `(1+a²+b²)^(-2) ≤ (1+a²)^(-1) (1+b²)^(-1)` | 86 |
| `summable_frequencyWeight_of_factors h1 hkey` | summability from the two factors (hypotheses) | 99 |
| `summable_frequencyWeight` | `Summable (fun k : ℤ × ℤ => (1 + k.1² + k.2²)^(-2 : ℤ))` | 108 |
| `exists_radius_eq_zero_of_isTestFunction hχ` | `∃ M, ∀ x ∉ ball 0 M, χ x = 0` | 113 |
| `abs_cutoffCosTest_le`, `abs_cutoffSinTest_le` | `\|cutoff test\| ≤ B` from `\|χ\| ≤ B` | 122, 129 |
| `cutoffCosTest_sq_le`, `cutoffSinTest_sq_le` | `test² ≤ χ²` pointwise | 136, 143 |
| `integrable_sq_of_isTestFunction hχ` | `Integrable (fun x => χ x ^ 2)` | 150 |
| `IsWholePlaneGFF.exists_integral_sq_cutoffTest_le hG hχ L` | `∃ C, 0 ≤ C ∧ ∀ k, ∫(hC cos_k)² ≤ C ∧ ∫(hC sin_k)² ≤ C` | 161 |
| `exists_measurable_conull_summable_of_tsum_lintegral_ne_top F hF0 hFm hfin` | generic Tonelli criterion: `∃ S, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ω ∈ S, Summable (F · ω)` | 189 |
| `IsWholePlaneGFF.exists_measurable_conull_cutoffFourier hG hχ L` | the weighted series is summable on `S` (one cutoff) | 206 |
| `IsWholePlaneGFF.ae_summable_cutoffFourier hG hχ L` | `∀ᵐ ω ∂P, Summable (...)` | 254 |
| `IsWholePlaneGFF.exists_measurable_conull_cutoffFourier_countable hG χ hχ L` | `{ι} [Countable ι]`: one `S` for all `i : ι` | 265 |

Binders, carrier and measure: `Ω : Type*` with `[MeasurableSpace Ω]`, `P : Measure Ω`, `hC : Ω → (ℂ → ℝ) → ℝ`,
`hcirc : Ω → ℝ → ℂ → ℝ`, `hG : IsWholePlaneGFF P hC hcirc`. Test functions live on `ℂ` (Lebesgue measure `volume`).
Frequencies live in `ℤ × ℤ`. The period `L : ℝ` is arbitrary: no `0 < L` hypothesis is assumed, because every
statement holds for every real `L` (none of the proofs uses the sign of `L`). The weight is the zpow
`(1 + (k.1 : ℝ)^2 + (k.2 : ℝ)^2)^(-2 : ℤ)`, that is, `(1 + |k|²)^{-2}` of the written argument.

## 3. Route (each step names its provider)

1. Test functions: `χ` times `cos`/`sin` of a smooth phase. Smoothness: `contDiff_cutoffPhase` (from `contDiff_const`,
   `Complex.reCLM.contDiff`, `Complex.imCLM.contDiff`); compact support: `HasCompactSupport.mul_right`; support in
   `univ`: `Set.subset_univ`.
2. Uniform bound: `IsWholePlaneGFF.integral_sq_pairing_le` (`RouteAPairingSecondMoment.lean:23`) with `f` a Fourier
   test, `M` from `exists_radius_eq_zero_of_isTestFunction` (compact support of `χ`, `HasCompactSupport.isCompact`,
   `Bornology.IsBounded.subset_closedBall`), and `B` from `Continuous.bounded_above_of_compact_support`. The pointwise
   bounds `|cos| ≤ 1`, `|sin| ≤ 1` give `∫ f² ≤ ∫ χ²` (`integral_mono_of_nonneg`). The constant is
   `C = (2 * kernelBoxConst M).toReal * ∫ χ²`, the same for every `k`.
3. Integrability: `GaussianCircleTestIntegral.memLp_pairing` (`GaussianCircleTestIntegral.lean:449`, namespace
   `HarmonicBalls.GaussianCircleTestIntegral`) gives `MemLp (hC · ψ) 2 P`; `MemLp.integrable_sq` gives the squares.
4. Lattice summability: `frequencyWeight_le_prod`, from `(1+a²+b²)² - (1+a²)(1+b²) = a⁴+b⁴+a²b²+a²+b² ≥ 0`; the
   one-dimensional weight via `Real.summable_one_div_int_pow` (`PSeries.lean:335`, namespace `Real`) and
   `Summable.of_norm_bounded_eventually` (`InfiniteSum.lean:182`); the product via `Summable.mul_of_nonneg`
   (`Ring/InfiniteSum.lean:34`). `summable_frequencyWeight` applies `summable_frequencyWeight_of_factors` to these two
   facts. The factored form is used because the direct form, with the constants inside the `exact` term, exceeded the
   per-declaration heartbeat budget (see section 6).
5. Almost-sure finiteness: `ofReal_integral_eq_lintegral_ofReal` (`Bochner/Basic.lean:734`), `lintegral_tsum`
   (`Lebesgue/Add.lean:362`), `Measurable.tsum`, `ae_lt_top'` (`Lebesgue/Markov.lean:154`),
   `ENNReal.summable_toReal` (`ENNReal.lean:350`), `ENNReal.ofReal_tsum_of_nonneg` (`ENNReal.lean:566`). The event is
   `S = {ω | ∑' k, ofReal(summand) < ⊤}`, which is measurable, with `P Sᶜ = 0` from `ae_iff`.
6. Countable cutoffs: `choose`, `MeasurableSet.iInter`, `Set.compl_iInter`, `measure_iUnion_null`.

Considered and not used: `EisensteinSeries.summable_one_div_norm_rpow` (`EisensteinSeries/Summable.lean:203`) is stated on
`Fin 2 → ℤ` with the sup norm, so it would need a transport along `finTwoArrowEquiv` and a sup-norm comparison;
`ZLattice.summable_norm_zpow` (`ZLattice/Summable.lean:264`) needs a `ℤ`-lattice in a normed space, which `ℤ × ℤ` is not
presented as here. The product majorant needs only the one-dimensional p-series.

## 4. Import closure

Transitive closure of the module (computed by following every `import HarmonicBalls.*` line; checked after `lb`):

- 22 `HarmonicBalls` modules, this one included: `Defs.{GFF, Green, LQG, LQGMetric, Laplacian, Notation}`,
  `Proofs.Potential.Fundamental`, `Proofs.Sec11.ClosureScales.{CircleAverageJointMeasurable, CirclePotential,
  CircleTestFubiniLimit, CutoffFourierSummability, GaussianCircleTestIntegral, MollifiedCircleGaussianL2,
  MollifiedContinuousCircleLimit, MollifiedLogCircleLimit, RootedShiftProfile, RouteACircleSmooth, RouteAKernel,
  RouteAKernelBox, RouteAPairingSecondMoment, UniversalRealization}`, and `Proposed.DuplantierMillerSheffield`.
- Non-Mathlib, non-`HarmonicBalls` imports: none. No module of `lattice-probability`, `MarkovProcess` or
  `EllipticRegularityLean` is in the closure, so this file needs no credit line to Leonardo Bonanno; it uses none of his
  code.
- `CircleTestIntegralL2Limit` is not in the closure (the independence requirement of the brief).
- `HarmonicBalls.Proposed.DuplantierMillerSheffield` (a staged literature input awaiting operator source-check) is
  imported transitively through existing ClosureScales modules. This file references none of its declarations
  (`DMSLemmaA`, `dmsConstant`, `dmsShift`, `dmsShiftedPairing`) and uses no `External` or `Proposed` Prop as a
  hypothesis. Its statements mention only `IsWholePlaneGFF`, `IsTestFunction` and the Fourier tests; its proofs use
  `IsWholePlaneGFF.integral_sq_pairing_le`, `kernelBoxConst` (in `exists_integral_sq_cutoffTest_le`) and
  `GaussianCircleTestIntegral.memLp_pairing`.

## 5. Remaining consumers (outside this task)

- The written argument's explicit validity test (`sec11-proof-r10.tex:1074` onward: cutoffs `χ_j = 1` on `B_j`, Fourier
  expansion of `χ_j g` on a torus) is not formalized here.
- The H^-2 reconstruction and the local H^-2 norm (`sec11-proof-r10.tex:1060`, `:1363-1365`) are not formalized here.
  This file provides only the almost-sure summability of the weighted coefficient series.
- `IsWholePlaneGFF.exists_measurable_conull_cutoffFourier_countable` is the countable intersection "intersect over the
  cutoffs" (`sec11-proof-r10.tex:1070-1071`) in the form it is used.

## 6. Checks

- `lc` (lock-free, `-DwarningAsError=true`), final file: CHECK OK.
- Compile history: the first versions timed out at `whnf` in `summable_frequencyWeight` (heartbeats are per declaration).
  The inline form was split into the factor lemmas above; a scratch test in the project header showed the hypothesis
  form elaborates within budget while using theorem constants inside the `exact` term did not. No `set_option` is used.
- Raw scan (`sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`, `unsafe`, `implemented_by`, `extern`,
  `set_option`, `opaque`, `partial`, `Bonanno`, `LatticeProb`; comments included): 0 hits.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CutoffFourierSummability`: BUILD OK (`logs/lb/003259-3957590.log`).
- Printed axioms (`#print axioms`), eight public declarations (`summable_frequencyWeight`, `isTestFunction_cutoffCosTest`,
  `isTestFunction_cutoffSinTest`, `IsWholePlaneGFF.exists_integral_sq_cutoffTest_le`,
  `exists_measurable_conull_summable_of_tsum_lintegral_ne_top`, `IsWholePlaneGFF.exists_measurable_conull_cutoffFourier`,
  `IsWholePlaneGFF.ae_summable_cutoffFourier`, `IsWholePlaneGFF.exists_measurable_conull_cutoffFourier_countable`): each is
  exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` (`logs/lc/003440-4042431.log`).

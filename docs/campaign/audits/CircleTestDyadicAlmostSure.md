# Almost-sure convergence of the dyadic circle-test integrals (audit)

Task: `sec11-dyadic-circle-test-almost-sure-limit`. Source: `notes/sec11-proof/sec11-proof-r10.tex` lines 1046-1061
(audited CORRECT): for a test `φ`, the limit `lim_{n→∞} ∫ c(2^{-n}, z) φ(z) d²z` is the pairing with the field, and
"this identity follows first in `L²` from the joint Gaussian covariance formula and then almost surely for our countable
family of tests and radii". Lines 1063-1090 (countable Fourier setting) are used only for the countable-family statement.

Scope: the almost-sure limit of the literal circle-test integrals for every whole-plane GFF `IsWholePlaneGFF P hC hcirc`
on `Ω : Type u`, for one test function, and for a countable family with one measurable conull event.
Not touched: H^-2 reconstruction, all-test samplewise identification, support/gluing, `RawToProfileStep`, the Palm
consumers, the frozen Draft statements, `HarmonicBalls.lean`, external and proposed inputs. No new input, admission,
carrier, GFF axiom, hypothesis, or numbered closure.

## Lean file

- `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleTestDyadicAlmostSure.lean` (new, 161 lines), namespace
  `HarmonicBalls.CircleTestDyadicAlmostSure`, `universe u`, `variable {Ω : Type u} [MeasurableSpace Ω]`.
  Direct imports: `HarmonicBalls.Defs.LQG`, `HarmonicBalls.Defs.Notation`, `HarmonicBalls.Proofs.Sec2.PolyHighProb`,
  `HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestIntegralL2Limit`,
  `HarmonicBalls.Proofs.Sec11.ClosureScales.SmoothCircleAverageRate`.

## Statements (binders as in the file)

- `dyadicScale_eq_zpow (n : ℕ) : dyadicScale n = (2 : ℝ) ^ (-(n : ℤ))`. Dyadic audit: `dyadicScale k := (2:ℝ)⁻¹ ^ k`
  (`Defs/LQG.lean:41`) is `2^{-k}` with no index offset; `k = 0` is the radius `1`.
- `measure_abs_ge_le_div_sq {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → ℝ} (hg : Integrable (fun ω => g ω ^ 2) P)
  {ε K : ℝ} (hε : 0 < ε) (hK : ∫ ω, g ω ^ 2 ∂P ≤ K) : P {ω | ε ≤ |g ω|} ≤ ENNReal.ofReal (K / ε ^ 2)`.
  Chebyshev via `mul_meas_ge_le_integral_of_nonneg`; the set need not be measurable.
- `polyHighProb_abs_lt_of_sq_integral_le {P : Measure Ω} [IsProbabilityMeasure P] {G : ℝ → Ω → ℝ} {C : ℝ}
  (hint : ∀ r : ℝ, 0 < r → r < 1 → Integrable (fun ω => G r ω ^ 2) P)
  (hbd : ∀ r : ℝ, 0 < r → r < 1 → ∫ ω, G r ω ^ 2 ∂P ≤ C * r ^ 2) {ε : ℝ} (hε : 0 < ε) :
  PolyHighProb P (fun r => {ω | |G r ω| < ε})`. The predicate `PolyHighProb` is `Defs/Notation.lean:27`
  (`∃ p > 0, ∃ C, ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → P (E r)ᶜ ≤ ENNReal.ofReal (C * r ^ p)`), instantiated with
  `p = 2`, `r₀ = 1`, constant `C / ε²`. `C ≥ 0` is not needed.
- `ae_tendsto_zero_dyadic_of_sq_integral_le {P} [IsProbabilityMeasure P] {G : ℝ → Ω → ℝ} {C : ℝ} (hint) (hbd) :
  ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => G (dyadicScale n) ω) atTop (𝓝 0)`. Uses
  `PolyHighProb.ae_eventually_dyadic` (`Proofs/Sec2/PolyHighProb.lean:75`, the project's Borel-Cantelli along the dyadic
  scales, reused and not re-proved) for each `ε_k = 1/(k+1)`, then `ae_all_iff` and `exists_nat_one_div_lt`.
- `ae_tendsto_circleTestIntegral_dyadicScale {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
  (hgff : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
  ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ w, hcirc ω (dyadicScale n) w * φ w) atTop (𝓝 (hC ω φ))`.
- `ae_tendsto_circleTestIntegral_two_zpow` (same binders): the same conclusion with the radius written literally as
  `hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) w`.
- `exists_measurable_conull_tendsto_circleTestIntegral_two_zpow {P} {hC} {hcirc} (hgff : IsWholePlaneGFF P hC hcirc)
  {ι : Type*} [Countable ι] (φ : ι → ℂ → ℝ) (hφ : ∀ i, IsTestFunction Set.univ (φ i)) :
  ∃ E : Set Ω, MeasurableSet E ∧ P Eᶜ = 0 ∧ ∀ ω ∈ E, ∀ i : ι,
  Tendsto (fun n : ℕ => ∫ w, hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) w * φ i w) atTop (𝓝 (hC ω (φ i)))`.
  Quantifier order as requested: family, then event, then all indices.

## Inputs used (all existing; none new)

- `SmoothCircleAverageRate.exists_second_moment_circleTestIntegral_le` (`SmoothCircleAverageRate.lean:127`), at universe
  `u`: a constant `C` depending only on `φ` with `∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ)^2 ∂P ≤ C * r^2` for every
  `Ω : Type u`, `P`, `IsWholePlaneGFF P hC hcirc`, and `0 < r ≤ 1` (the file uses `r < 1`).
- `IsWholePlaneGFF.memLp_circleTestIntegral_sub` (`CircleTestIntegralL2Limit.lean:321`): `MemLp _ 2 P` of the error for
  `0 < r ≤ 1`; gives integrability of the square for Chebyshev.
- `IsWholePlaneGFF.isProbabilityMeasure` (`Defs/GFF.lean:185`).
- `PolyHighProb` (`Defs/Notation.lean:27`) and `PolyHighProb.ae_eventually_dyadic` (`Proofs/Sec2/PolyHighProb.lean:75`).
- Mathlib: `mul_meas_ge_le_integral_of_nonneg` (`MeasureTheory/Integral/Bochner/Basic.lean:1162`), `ae_all_iff`
  (`OuterMeasure/AE.lean:152`), `ae_iff`, `exists_measurable_superset_of_null` (`Measure/MeasureSpaceDef.lean:219`),
  `measureReal_mono`, `measureReal_def`, `measure_ne_top`, `ENNReal.ofReal_toReal`, `ENNReal.ofReal_le_ofReal`,
  `Real.rpow_two`, `exists_nat_one_div_lt` (`Algebra/Order/Archimedean/Basic.lean:214`), `Metric.tendsto_nhds`,
  `tendsto_sub_nhds_zero_iff`, `MemLp.integrable_sq` (`MeasureTheory/Function/L2Space.lean:42`), `ae_iff`.
- Reuse search: the project's Borel-Cantelli helpers were checked (`Steps/Sec11/AnnulusBorelCantelli.lean`,
  `Proofs/Sec2/PolyHighProb.lean`). `PolyHighProb.ae_eventually_dyadic` matches the dyadic form and is used.
  `Proofs/Sec11/ClosureScales/CircleTestIntegralConvergenceLocus.lean` is the Borel locus on the canonical carrier
  `C(CircleDomain, ℝ)`, a different statement; it is not used.

## Proof route and what is not claimed

- Route: second-moment rate, Chebyshev on the square, `PolyHighProb` with exponent 2, Borel-Cantelli along the
  dyadic scales (project lemma), countable intersection over the accuracies `1/(k+1)`.
  For a family, the countable intersection over `i` gives an almost-sure statement, and a measurable conull superset of
  its exceptional set (`exists_measurable_superset_of_null`) gives the measurable event `E := tᶜ`.
- Measurability of the approximants `ω ↦ ∫ w, hcirc ω (dyadicScale n) w * φ w` is neither used nor claimed. The event
  is measurable because its complement is a measurable null superset.
- Not claimed: samplewise linearity of `hC`, identification for non-test functions, `H^-2` reconstruction, support or
  gluing, `RawToProfileStep`, or any canonical sample space.

## Import closure, credit, consumers

- Transitive closure (walk over the `import` lines of project modules, Mathlib, Batteries and Lean skipped; script
  `scratch/z3probe/closure.py`, untracked): 26 modules, all `HarmonicBalls`; 0 `LatticeProb` / Bonanno modules. So no
  Bonanno credit line is required in this file.
- Consumers: none in `HarmonicBalls` at this commit (grep for the new names finds only the file itself).

## Checks

- `lc` on the file: CHECK OK (warnings are errors), log `logs/lc/044746-1651305.log`.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestDyadicAlmostSure`: BUILD OK, log `logs/lb/044808-1688016.log`.
- Printed axioms of the seven public and auxiliary declarations: `[propext, Classical.choice, Quot.sound]` (probe
  `scratch/z3probe/DyadicAxioms.lean`, untracked).
- Raw scan of the Lean file for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `extern`, `implemented_by`,
  `maxHeartbeats`, `maxRecDepth`, `set_option`, `ofReduceBool`, `opaque`, `initialize`, `#exit`, `run_cmd`,
  `unsafeCast`, `decide`, `kernel`, `private`, `partial`: 0 hits. Comment-aware: no hits in comments either.

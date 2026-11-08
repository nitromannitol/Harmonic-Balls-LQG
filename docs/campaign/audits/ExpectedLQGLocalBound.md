# Audit: ExpectedLQGLocalBound (zero-charge LQG, expectation-level local domination)

Task: `zero-charge-lqg-expected-measure-local-domination` (worker z3, round 1).
Module: `HarmonicBalls/Proofs/Sec11/ExpectedLQGLocalBound.lean` (new). It imports
`HarmonicBalls/Proofs/Sec11/FixedSquareFrontierNull.lean` (first-moment cutoff bound
`IsWholePlaneGFF.lintegral_lqgMeasure_le_of_cutoff`, `exists_cutoff_of_isCompact`) and
`HarmonicBalls/Proofs/Sec5/OpenMeasureLaw.lean` (`IsWholePlaneGFF.aemeasurable_lqgMeasure`); both are reused unchanged.
No existing file is edited.

## Status

- `lc`: CHECK OK (`lake env lean -DwarningAsError=true`).
- `lb HarmonicBalls.Proofs.Sec11.ExpectedLQGLocalBound`: BUILD OK (log `/home/nitro/paper-fleets/hb/logs/lb/032944-2044190.log`).
- Forbidden-token scan of the module (`sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`, `set_option`):
  0 hits.
- `#print axioms` (probe file `/tmp/z3-axioms-ELB/Axioms.lean` outside the repository, `lake env lean`):
  `[propext, Classical.choice, Quot.sound]` for `lintegral_lqgMeasure_le_volume_of_measurableSet`,
  `lintegral_lqgMeasure_le_volume_of_isCompact`, `isFiniteMeasureOnCompacts_bind` and `zeroChargeLocalConst`.

## Statement (namespace `HarmonicBalls`)

- `zeroChargeLocalConst γ R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (max R 0 + 1)))`, the deterministic
  constant `(max R 0 + 1)^{γ²}`. It depends only on `γ` and `R`, not on `ω` or `A`.
- `IsWholePlaneGFF.lintegral_lqgMeasure_le_volume_of_isCompact` (compact sets). Inputs: `hgff : IsWholePlaneGFF P hC hcirc`,
  `hμ : IsLQGMeasureOfField P γ 0 hcirc μ`, `hK : IsCompact K`, `hKR : K ⊆ Metric.ball 0 R`. Conclusion:
  `∫⁻ ω, μ ω K ∂P ≤ zeroChargeLocalConst γ R * volume K`.
- `IsWholePlaneGFF.isFiniteMeasureOnCompacts_bind`: `IsFiniteMeasureOnCompacts (P.bind μ)`, i.e. `ν K < ∞` for compact
  `K`, where `ν = P.bind μ` is the expectation measure `ν B = ∫⁻ ω, μ ω B ∂P` (proved finite via the compact bound).
- `IsWholePlaneGFF.lintegral_lqgMeasure_le_volume_of_measurableSet` (main). Inputs as above, with
  `hA : MeasurableSet A`, `hAR : A ⊆ Metric.ball 0 R`. Conclusion:
  `∫⁻ ω, μ ω A ∂P ≤ zeroChargeLocalConst γ R * volume A`.

Quantifier order: `R`, `A` (and `K`) are fixed before `ω`. The bound is a single `lintegral` inequality for each fixed
`A`; no `P`-null set is introduced or used, and no statement quantifies over `ω` before `A`.

## Route

1. Compact `K ⊆ ball 0 R`: put `R₀ = max R 0`. `IsCompact.exists_cthickening_subset_open` gives `δ₀ > 0` with
   `cthickening δ₀ K ⊆ ball 0 R₀`. For `0 < δ ≤ δ₀`, `exists_cutoff_of_isCompact` gives a continuous `f`, `0 ≤ f ≤ 1`,
   `f = 1` on `K`, `f = 0` off `cthickening δ K`, and `∫⁻ f ≤ vol (cthickening δ K)`. Then `f = 0` for `‖z‖ > R₀`, and
   `lintegral_lqgMeasure_le_of_cutoff` gives `E μ(K) ≤ (R₀+1)^{γ²} ∫⁻ f ≤ (R₀+1)^{γ²} vol(cthickening δ K)`.
   Letting `δ → 0` within `𝓝[>] 0` (`tendsto_measure_cthickening_of_isCompact`, `ge_of_tendsto`) gives the compact bound.
2. Borel `A ⊆ ball 0 R`: `ν = P.bind μ` (`Measure.bind_apply`, from `AEMeasurable μ P`). `ν` is finite on compacts (step 1),
   hence regular (instance `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`), and `ν A ≠ ∞` because `A` lies in
   a compact closed ball. So `ν A = ⨆ K ⊆ A compact, ν K`
   (`MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`). Each term is `≤ zeroChargeLocalConst γ R * vol K ≤
   zeroChargeLocalConst γ R * vol A` by step 1 and `K ⊆ A`.

This is the alternative route named in the task (existing cutoff bound on compact `K`, plus inner regularity of the
expected locally finite measure). Measurability and local finiteness of `ν` are proved here, not assumed:
measurability of `ω ↦ μ ω B` comes from `AEMeasurable μ P` (`IsWholePlaneGFF.aemeasurable_lqgMeasure`), and local
finiteness from step 1. The open-set route (increasing compact exhaustion of open sets plus `lintegral_iSup'`) was not
needed.

## Scope and non-claims

- This is expectation-level domination. It does not assert `μ ω ≪ volume` for any `ω`, and it does not interchange a
  fixed-`A` bound with a samplewise universal-`A` null event.
- Hypotheses: `hgff` and `hμ` only. No bound `0 < γ < 2`, no `α₀ < lqgQ γ` (`α₀ = 0` here), no normalization of `P`.
- Statements are `lintegral`s of `ENNReal`-valued functions, so no Bochner integrability is used.
- No literature input: nothing from `HarmonicBalls/External` or `HarmonicBalls/Proofs/Proposed` is used.
- No frozen definition or Draft statement is changed. `Defs`, `Draft`, `FROZEN`, `External`, `Proposed`, the paper and
  `Closure/` are untouched.
- Not covered: the Lebesgue-null sets of the singular-LQG task (`SingularCompactNull`); that task is independent.

## Credit

Leonardo Bonanno: the import closure of the module contains code by Leonardo Bonanno. It reaches the external
LatticeProb module `LatticeProb.Prob.Birkhoff` through `HarmonicBalls/Proofs/Sec8/BirkhoffPort.lean` (which imports
`LatticeProb.Prob.Birkhoff` directly). Checked by reading the import lines: `FixedSquareFrontierNull` imports
`Sec8.ConcentricCircleCovariance` and `Sec8.CircleLogPotential`, and its closure reaches `Sec8/BirkhoffPort`, as
recorded in `docs/campaign/audits/SingularCompactNull.md` (line 68-69). The new module's closure contains that closure.
The added import `Sec5/OpenMeasureLaw` (which imports `Sec5/LQGIntegralLaw` and Mathlib) was not traced separately for
further credited code; the credit paragraph names Leonardo Bonanno as in `FixedSquareFrontierNull.lean` and
`SingularCompactNull.lean`, and the module docstring carries it.

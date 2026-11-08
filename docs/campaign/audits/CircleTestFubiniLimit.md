# Audit: CircleTestFubiniLimit (task sec11-circle-test-fubini-limit)

Module: `HarmonicBalls/Proofs/Sec11/ClosureScales/CircleTestFubiniLimit.lean` (new, 493 lines, namespace
`HarmonicBalls.CircleTestFubini`).
Source: r10 written argument, `notes/sec11-proof/sec11-proof-r10.tex` lines 1353-1378 (R direction of
`l:r9-circle-code`): Fubini moves the circle average onto the smooth compact test, `|r| ≤ 1` gives one compact
enlargement, and the averaged tests converge. The task's citation of `AUDIT-r9.md` rows 999-1025 and `AUDIT-r10.md:110`
could not be re-located: `AUDIT-r9.md` has 157 lines and no audit file contains `1353` or `1378`. The written argument
was therefore checked directly at the cited TeX lines, not through an audit table.

## Scope

Deterministic only. No probability space, no field, no event, no literature input. Not claimed: the H^-2
reconstruction or summability step, convergence in the full smooth test topology (only the scalar limit is proved, as
the task asks), identification with the raw `hC`, the E56 `RawToProfileStep`/`CanonicalProfile` carrier, or any
numbered result.

## Statements

Line numbers are in the new file.

| Declaration | Line | Content |
|---|---|---|
| `testEnlargement` | 43 | `tsupport φ + Metric.closedBall 0 1`, the fixed compact enlargement |
| `isCompact_testEnlargement` | 52 | it is compact |
| `isTestFunction_circleAverage` | 136 | `|r| ≤ 1`: `φ_r = Real.circleAverage φ · r` is `IsTestFunction (testEnlargement φ)` |
| `isTestFunction_univ_circleAverage` | 142 | same, as `IsTestFunction univ` |
| `fixed_enlargement_circleAverage` | 150 | bundle: compact enlargement, and for `0 < r ≤ 1` both test memberships |
| `norm_circleAverage_le` | 160 | `‖φ_r v‖ ≤ M` when `‖φ‖ ≤ M` |
| `tendstoUniformly_circleAverage` | 174 | `TendstoUniformly (fun r v => φ_r v) φ (𝓝[>] 0)` (uniform convergence) |
| `tendsto_circleAverage_test` | 213 | pointwise `φ_r v → φ v` (from the uniform statement) |
| `integrable_kernel` | 249 | absolute integrability of `(θ, v) ↦ g v · φ(v - r e^{iθ})` on `(0,2π] × ℂ` (measurable `g`) |
| `integral_circleAverage_mul_eq_of_measurable` | 278 | Fubini, measurable `g`: integrability of `w ↦ ⨍ g · φ` and `∫ w, ⨍_{∂B(w,r)} g · φ = ∫ v, g v · φ_r v` |
| `ae_circleAverage_eq_of_ae_eq` | 348 | changing `g` on a null set changes its circle averages only on a null set of centres |
| `integral_circleAverage_mul_eq` | 378 | the same for every `LocallyIntegrable g`, with absolute integrability of both sides |
| `tendsto_integral_circleAverage_mul` | 403 | **`Tendsto (fun r => ∫ w, ⨍_{∂B(w,r)} g · φ w) (𝓝[>] 0) (𝓝 (∫ v, g v · φ v))`** for every `LocallyIntegrable g` |
| `tendsto_integral_continuous_circleAverage_mul` | 427 | instance: every continuous `u`, the test `φ` fixed first |
| `locallyIntegrable_dmsShift` | 435 | `dmsShift γ z` is locally integrable, from its definition |
| `circleAverage_dmsShift` | 455 | **literal formula** `⨍_{∂B(w,r)} dmsShift γ z = -γ log (max r ‖w - z‖) + γ ⨍_{∂B(w,r)} logMaxOne`, `0 < r`, every `w` (circles through `z` included) |
| `tendsto_integral_dmsShift_circleAverage_mul` | 474 | instance: the limit against `φ` for `dmsShift γ z` |
| `tendsto_integral_dmsShift_literal` | 482 | the same limit with the literal formula inside the integral |

Quantifier order: in every instance the test `φ` (with `IsTestFunction univ φ`) comes first, then `z` or `u`
(continuous), then the radius limit. `γ : ℝ` is arbitrary.

## Route

1. Circle averages as `(2π)⁻¹ ∫_{(0,2π]}` (`circleAverage_eq_Ioc`). Reflection through the centre,
   `∫ φ(v - c θ) dθ = ∫ φ(v + c θ) dθ`, from the half-period shift and periodicity (`setIntegral_sub_circle_eq`).
2. Kernel `H(θ,v) = g v · φ(v - cθ)` is integrable on `angleMeasure × volume` by domination by
   `M · |g| · 1_{testEnlargement φ}` and `Integrable.mul_prod`.
3. The shear `(θ, w) ↦ (θ, w + cθ)` is measure preserving (`MeasurePreserving.skew_product`, translation invariance),
   so `F = H ∘ shear` is integrable. Two applications of `integral_integral_swap` and one translation
   (`integral_add_right_eq_self`) give the identity for measurable `g`.
4. Arbitrary `LocallyIntegrable g`: replace `g` by the measurable `g'` from `aestronglyMeasurable.mk`. The circle
   averages of `g` and `g'` agree for a.e. centre, because `{g ≠ g'}` lies in a measurable null set `t` and the set
   `{(w,θ) : w + cθ ∈ t}` has measure zero (`Measure.prod_apply_symm`, `measure_preimage_add_right`,
   `Measure.ae_ae_of_ae_prod`).
5. Limit: dominated convergence on `𝓝[>] 0` (`tendsto_integral_filter_of_dominated_convergence`), bound
   `M · 1_{testEnlargement φ} · |g|` (the common compact support), pointwise limit from the uniform convergence
   `φ_r → φ` (uniform continuity of `φ`, `Metric.uniformContinuous_iff`).
6. `dmsShift`: `circleAverage_fun_add` with `circleIntegrable_log_norm_sub_const` and the continuous `logMaxOne`;
   the logarithmic circle average is `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max` (Sec11 `CirclePotential.lean:24`).

## Inputs and imports

- Definitions only from the project: `IsTestFunction` (`Defs/Laplacian.lean:47`), `dmsShift`
  (`Proposed/DuplantierMillerSheffield.lean:34`, definition only; no `Prop` from `Proposed` is used or assumed),
  `logMaxOne` (`RootedShiftProfile.lean:23`), `contDiff_circleAverage_of_contDiff` (`RouteACircleSmooth.lean:73`),
  `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max` (`CirclePotential.lean:24`), `integrableOn_ball_log_norm` and
  `locallyIntegrable_comp_sub_of_integrableOn_ball` (`Potential/Fundamental.lean:44, 67`).
- Import closure: 12 `HarmonicBalls` modules, checked by a transitive `^import` walk. No `LatticeProb` module, no
  Sec8 module, and no file in the closure mentions Bonanno. So no Bonanno credit line is required, and the
  `LogInsertionReconstruction.lean` route was not taken.
- Name collision, resolved. The unqualified last name `circleAverage_log_norm_sub_eq_log_max` was shared by the
  Section 8 declaration `HarmonicBalls.circleAverage_log_norm_sub_eq_log_max` (`Proofs/Sec8/CircleLogPotential.lean:17`,
  unchanged) and the Sec11 declaration `HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max`
  (`Proofs/Sec11/ClosureScales/CirclePotential.lean:24`, in namespace `HarmonicBalls.CirclePotential` since commit
  2e35bf4). Every citation now uses a qualified name, so the clash no longer arises. This file imports only the Sec11
  declaration.
- No hypothesis of the form "the additions satisfy a bound, convergence or integrability" appears anywhere; the
  continuous and logarithmic additions enter only through their own definitions.

## Checks

- `lc` (warnings as errors, project options): `CHECK OK`, no `sorry` warning.
- `lb HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestFubiniLimit`: `BUILD OK`.
- `#print axioms` (scratch file under `/tmp`, `lake env lean`): every public declaration in the table above depends only
  on `propext`, `Classical.choice`, `Quot.sound`.
- Raw scan of the file for `sorry`, `admit`, `native_decide`, `axiom`, `maxHeartbeats`, `set_option`, `unsafe`,
  `implemented_by`, `extern`: zero hits. Since the raw scan is empty, the comment-aware scan is also empty.

## Points for the reviewer

- `0 < r ≤ 1` in the task is proved as `|r| ≤ 1`. This is a generalization, not a weakening: the test-function,
  Fubini and limit statements all hold for every `|r| ≤ 1`, and the positive case is what the instances use.
- The written argument says `φ * σ_{r,0} → φ` in the smooth test topology. This file proves only the scalar limit
  `∫ g · φ_r → ∫ g · φ` that the task asks for, via uniform convergence plus common compact support. The smooth
  topology statement is not claimed.
- Measurability of `g` is not assumed: the general statement is reduced to the measurable representative (point 4
  of the route).

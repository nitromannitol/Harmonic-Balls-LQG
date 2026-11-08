# ClosureMeasureMeasurable (task section11-discharge-proved-measure-measurability, worker z3)

Module: `HarmonicBalls/Proofs/Sec11/ClosureMeasureMeasurable.lean` (new; outside `Closure/`; not imported by
`HarmonicBalls.lean`, since the task forbids umbrella edits).

Target: the Type-zero body of Lemma 11.12 at `α₀ = 0` (`PinchEventPositiveProbabilityStmt`,
`HarmonicBalls/Draft/Section11.lean:246`). The result is conditional on raw canonical positivity. It is not a closure of
Lemma 11.12, and no frozen statement, definition, input or paper file was changed.

## Declarations

| Declaration | Line | Premises | Conclusion |
|---|---|---|---|
| `pinchEventPositive_typeZero_of_raw_gff` | 38 | `hconfig : IsPinchPointConfiguration U T Q' Q`, `hraw : RawCanonicalPositiveStmt U T Q' Q` | the `∀ γ ξ … ∀ Ω : Type …` body with `pinchPointEvent` and `∃ A ⊆ …, MeasurableSet A ∧ 0 < P A` |
| `exists_pinchEvent_typeZero_fixed_of_raw_gff` | 82 | `hraw : RawCanonicalPositiveStmt fixedU fixedT fixedQ' fixedQ` | `∃ U T Q' Q, IsPinchPointConfiguration U T Q' Q ∧ ∀ γ ξ …` (fixed configuration) |

The only premise is raw canonical positivity (`Closure/PinchEventTypeZero.lean:25`) for the given configuration. There is
no `haem`, no locality premise, no literature input and no Proposed input.

## Route

- `haem` (`Closure/PinchEventTypeZero.lean:37-38`) is removed. Its universal binder ranges over all `γ, Ω, P, hcirc, μ`
  and does not contain `IsWholePlaneGFF P hC hcirc`, so the GFF hypothesis of the configuration cannot discharge it.
- Replacement: `hgff.aemeasurable_lqgMeasure hμ`, using `IsWholePlaneGFF.aemeasurable_lqgMeasure`
  (`Proofs/Sec5/OpenMeasureLaw.lean:130`): `{Ω : Type*} … (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) : AEMeasurable μ P`.
  It has no locality premise and holds for arbitrary `α₀` and universe.
- Reused unchanged: `ae_metric_eq_canonical_of_isLQGMetricOfField_zero` (`Closure/MetricBridgeZero.lean:38`),
  `ae_isEuclideanLengthMetric_of_isLQGMetricOfField_zero` (`Closure/MetricBridgeZero.lean:55`),
  `measurable_canonical_metric` (`Closure/MetricMeasurableZero.lean:32`), `exists_measurable_pos_subset_pinch`
  (`Proofs/Sec11/PinchInnerPositivity.lean:38`), the `toMeasurable` null-set removal, and `isPinchPointConfiguration_fixed`
  (`Closure/FixedGeometry.lean:252`).
- Statements: the header of `pinchEventPositive_typeZero_of_raw` differs from the new header only by the removed `haem`
  binder and the name (checked by an `awk`-extracted `diff`). The fixed export matches
  `exists_pinchEvent_typeZero_fixed_of_raw` with `haem` removed. Carriers, the `Ω : Type` restriction, the
  `∃ A ⊆ …` null-set quantifier order and the conclusion are unchanged.

## Checks

- `lc`: CHECK OK. `lb HarmonicBalls.Proofs.Sec11.ClosureMeasureMeasurable`: BUILD OK (run after the final docstring edit).
- `#print axioms`: both declarations depend on `[propext, Classical.choice, Quot.sound]` (lc log).
- Forbidden-token scan (`sorry`, `axiom`, `admit`, `native_decide`, `maxHeartbeats`, `opaque`, `unsafe`,
  `implemented_by`) on the file: no match.
- The two names were unused in the repository before this round.

## Import closure

Imports: `Closure/PinchEventTypeZero` and `Sec5/OpenMeasureLaw`. The closure of these two roots (computed from the
`import` lines) has 349 `HarmonicBalls` modules, 57 Mathlib modules and these external modules: `LatticeProb.Prob.Birkhoff`
and the `MarkovProcess` modules (Brownian motion, killed process, exit law). The module adds no import of its own beyond
the two roots.

## Credit

The module docstring names Leonardo Bonanno. The Bonanno code in the closure is `LatticeProb.Prob.Birkhoff` (his
LatticeProb formalization of the ergodic theorem, credited in `Steps/Sec11/CountableCoordinateObservables.lean`) and
`Proofs/Sec11/WholePlaneMetricLocality.lean` (its Section 8 inputs use his LatticeProb code), reached through
`Closure/MetricBridgeZero.lean`.

## For z6

- `Closure/RandomMeasureMeasurable.lean` (`aemeasurable_lqg_measure_zero_of_locality`,
  `pinchEventPositive_typeZero_of_raw_locality`) discharges `haem` from the staged `LQGMeasureLocality`. That locality
  premise is not needed: `IsWholePlaneGFF.aemeasurable_lqgMeasure` gives `AEMeasurable μ P` with no locality hypothesis.
  Consumers can use `pinchEventPositive_typeZero_of_raw_gff` and `exists_pinchEvent_typeZero_fixed_of_raw_gff`, whose only
  premise is `RawCanonicalPositiveStmt`.
- Nothing under `Closure/` was edited.

## Not done

- Lemma 11.12 is not closed: `RawCanonicalPositiveStmt` (raw canonical positivity of the strengthened pinch event at
  `α₀ = 0`) remains a premise.
- Not added to `HarmonicBalls.lean` (umbrella edits forbidden for this task).

# Section 9 three-input numbered export (worker z4)

Task `section9-three-input-numbered-export-assembly`. Files: `HarmonicBalls/Proofs/Sec9/ThreeInputAssembly.lean`
(new), `archive/HarmonicBalls/Audit/Section9ThreeInputChecks.lean` (new), this note.

## Exports

| Declaration | Conclusion (frozen Draft statement) | Explicit binders |
|---|---|---|
| `section9_comparison_results_of_three_inputs` | `ObstacleComparisonStmt`, `HarmonicBallBoundarySubsetStmt`, `RegularOpenEqOfAEEqStmt` (Lemmas 9.1, 9.3, 9.4) | `hDG hCC hE` |
| `section9_numbered_results_of_three_inputs` | the three above and `SubharmonicBallUniquenessWeakStmt` (weak Proposition 9.2) | `hDG hCC hE h82` |

Staged inputs: `hDG` = `WholePlaneLQGBallMassBounds` (fixes insertion 0 in its statement); `hCC` =
`LQGMeasureCoordChange P γ 0` (insertion 0); `hE` = `LQGMeasureExistence P γ α` (all `α`). These are the
source-checked inputs (operator file `audits/PROPOSED-LQG-SOURCE-CHECK-20261108.md`, rows 10, 14, 15: FAITHFUL, CONFIRMED).

## Routes

* Lemma 9.1: `obstacleComparison` (`HarmonicBalls/Proofs/Sec9/ObstacleComparison.lean:32`), no hypotheses.
* Lemmas 9.3 and 9.4: `section9_comparison_lemmas_of_existence` (`Proofs/Sec9/ExistenceResultsAssembly.lean:51`).
* Weak Proposition 9.2: `subharmonicBallUniquenessWeak_of_existence` (`ExistenceResultsAssembly.lean:59`).

Predecessors discharged inside these producers, so they are not binders:

* I2 `LQGVolumeGrowthAllScalesStmt`: `lqgVolumeGrowthAllScalesStmt_of_existence` (`ExistenceResultsAssembly.lean:36`).
* Affine invariance: `wholePlaneGFFAffineInvariance_proved` (`Proofs/Sec9/AffineInvarianceAssembly.lean:21`).
* Weyl scaling: `Section6.lqgMeasureWeylScaling` (`Proofs/Sec6/LQGWeylScaling.lean:124`).
* Non-atomicity: `Section6.lqgMeasureNonatomic_of_existence` (`Proofs/Sec6/SingularityOriginNonatomic.lean:94`).
* Lemma 6.11 (`VeryGoodAnnulusHarnackTypeStmt`) on the dyadic route, derived from I2 by
  `Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure` (`Proofs/Sec9/DyadicGlobalUniqueness.lean:35`).

The Section 6 three-input exports (`Proofs/Sec6/FullThreeInputAssembly.lean`, for example
`veryGoodAnnulusHarnackTypeStmt_of_three_inputs`) are not used: the existing Section 9 chain already derives
Lemma 6.11 from I2, and a second source would only duplicate it.

## Leaves

* `h82 : TypicalPointManyGoodScalesStmt` (Lemma 8.2, `Draft/Section8.lean:74`). This is the one genuine
  missing leaf of the numbered export. It is an explicit binder, not a literature input.
  Lemma 8.2 reduces further to `hcomparison` through `typicalPointManyGoodScalesStmt_of_literature`
  (`Proofs/Sec8/TypicalPointLiteratureAssembly.lean:24`). That route is not used: the task forbids assuming
  `hcomparison`, and it takes the coordinate change at every insertion `α`, not at `0`.
* No boundary-nullity binder. The dyadic route needs only I2 and `h82`; `ClusterBoundaryNullAllRadii` and
  `BoundaryMeasureZeroOfCompactClusterStmt` are not binders of any export.

## Exclusions

* Ordinary Proposition 9.2, `SubharmonicBallUniquenessStmt` (`Draft/Section9.lean:109`): not exported. Its first
  conclusion `int(closure Λ) ⊆ A` is not shown by the printed proof ([C10]; operator decision E33(a)).
* Lemma 10.1 (`clusterBoundedCrossings_of_existence`, `ExistenceResultsAssembly.lean:65`): outside this task's scope and not re-exported.

## Scope

* Coordinate change: only insertion `0` is consumed. The all-insertion scope is not used by any export; the
  audit checks that the single `LQGMeasureCoordChange` occurrence is applied at the literal `0`.
* Frozen conclusions are used unchanged: carriers `Ω : Type u`, AE order `∀ᵐ ω ∂P`, Green orientation
  `greenFunction (ball 0 R) x z`, physical-dimension range `0 < γ < 2`, `α₀ < lqgQ γ`.

## Checks

* `lc` passes for both files. `lb HarmonicBalls.Proofs.Sec9.ThreeInputAssembly` reports BUILD OK.
* Audit (MetaM and typed examples): exact binder names, all explicit; required conclusion constants present;
  forbidden constants (ordinary 9.2, I2, affine/Weyl/non-atomicity, Lemma 6.11, boundary nullity, Lemma 10.1 subrange
  step) absent from the export types; insertion `0`; axioms only `propext`, `Classical.choice`, `Quot.sound`.
* Code scan: no `sorry`, `admit`, `native_decide`, `set_option`, or `axiom` declaration.

## Open items for the operator

1. Operator to confirm the all-α₀ scope of `LQGMeasureCoordChange` (source-check row 14 and the round-10 note).
   These exports do not use it. The `hcomparison` route above would need it.
2. `ExistenceResultsAssembly.lean` header says the three inputs "await source review". They are now source-checked.
   That file is not owned by this task and was not edited.
3. `Audit/Section9ComparisonExports.lean` (another worker's file) audits the same existence producers conditionally.
   This audit adds the binder, insertion and forbidden-constant checks, and does not repeat its examples.

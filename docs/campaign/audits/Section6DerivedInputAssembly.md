# Section 6 derived input assembly: Propositions 6.1-6.2 with the Weyl premise discharged, and Lemma 6.12

TASK: section6-discharge-derived-weyl-premise (worker z3, Claude Haiku 5.5, 2026-11-07). Lean file:
`HarmonicBalls/Proofs/Sec6/DerivedInputAssembly.lean` (new). Lean only. No frozen statement, staged premise, existing
export, c2 provider, `Proposed` or `External` file is edited. This is an improved conditional assembly. It does not
close Proposition 6.1 or Proposition 6.2.

## Result

* `lc HarmonicBalls/Proofs/Sec6/DerivedInputAssembly.lean`: CHECK OK. `lb HarmonicBalls.Proofs.Sec6.DerivedInputAssembly`:
  BUILD OK (`/home/nitro/paper-fleets/hb/logs/lb/014603-1826913.log`: 0 errors; no warning from the module).
* Forbidden-token scan on the new file (`sorry`, `admit`, `native_decide`, `maxHeartbeats`, `axiom` declarations,
  `unsafe`, `implemented_by`, `extern`): no match.
* Printed axioms: each of the six declarations (four exports, Lemma 6.12 export, Weyl provider) depends only on
  `propext`, `Classical.choice` and `Quot.sound`.
* Weyl premise `hW`: discharged internally. `lqgMeasureWeylScaling_univ` is `HarmonicBalls.Section6.lqgMeasureWeylScaling`
  (`HarmonicBalls/Proofs/Sec6/LQGWeylScaling.lean:124`) at `α₀ = 0` and every carrier `Ω : Type u`, with no further
  premise. The exports take no `LQGMeasureWeylScaling` hypothesis (meta guard). Consequence: the Weyl Prop of
  `HarmonicBalls/Proposed/LQG.lean:93` is no longer a staged premise of Propositions 6.1-6.2.
* Affine premise: none occurs in this route. `HarmonicBalls/Proofs/Sec6/Assembly.lean` takes no
  `WholePlaneGFFAffineInvariance`, so `wholePlaneGFFAffineInvariance_proved` is not used.
* Lemma 6.12: `shellDecompositionStmt_of_proved : ShellDecompositionStmt` (no premise), from
  `shellDecompositionStmt_proved` (`HarmonicBalls/Proofs/Sec6/ShellDecomposition.lean:164`).

## Exports at the frozen statements

| export (`HarmonicBalls.Section6Derived.`) | frozen Stmt (`HarmonicBalls/Draft/Section6.lean`) | explicit hypotheses |
|---|---|---|
| `harnackTypeEstimateStmt_of_derived_weyl` | Prop 6.1 `HarnackTypeEstimateStmt` (:206) | `hsub`, `hex`, `h32`, `h68`, `h610`, `h613` |
| `harnackTypeComponentStmt_of_derived_weyl` | Prop 6.2 `HarnackTypeComponentStmt` (:230) | `hsub`, `hex`, `h32`, `h68`, `h610`, `h613` |
| `harnackTypeEstimateStmt_of_derived_weyl_steps` | Prop 6.1 | `hsub`, `hex`, `h32`, `h68`, `h610`, `hdec`, `hdisc` |
| `harnackTypeComponentStmt_of_derived_weyl_steps` | Prop 6.2 | `hsub`, `hex`, `h32`, `h68`, `h610`, `hdec`, `hdisc` |
| `shellDecompositionStmt_of_proved` | Lemma 6.12 `ShellDecompositionStmt` (:442) | none |
| `lqgMeasureWeylScaling_univ` (provider) | `LQGMeasureWeylScaling P γ 0 hC hcirc` (`Proposed/LQG.lean:93`) | none |

The explicit leaves are kept at their existing exact Props (`hsub`, `hex`, `h32`, `h68`, `h610` and `h613` are the leaves
of `harnackTypeComponentStmt_of_inputs` and `harnackTypeEstimateStmt_of_inputs`, `Proofs/Sec6/Assembly.lean`):

* `hsub`: `VeryGoodAnnuliSubRangeStep` (`HarmonicBalls/Steps/Sec6/Prevalence.lean:54`).
* `hex`: `LQGMeasureExistence P γ 0` (staged in `HarmonicBalls/Proposed/LQG.lean:66`, pending operator source-check).
* `h32`: `ClusterOpenLaplacianStmt` (Lemma 3.2, `HarmonicBalls/Draft/Section3.lean:66`).
* `h68`: `AnnulusMassBoundByOdometerStmt` (Lemma 6.8, :352); `h610`: `OdometerBoundByAnnulusMassStmt` (Lemma 6.10, :388).
* `h613`: `LowMassSmallOdometerStmt` (Lemma 6.13, :462), or in the `_steps` variants its two steps
  `GoodAnnulusOdometerDecayStep` (`HarmonicBalls/Steps/Sec6/LowMass.lean:35`) and `ComponentOdometerDiscMaxStep`
  (`:48`), through `lowMassSmallOdometerStmt_of_steps` (`HarmonicBalls/Proofs/Sec6/LowMass.lean:120`).

## Overlaps with existing reductions (reported, not duplicated)

1. `HarmonicBalls/Proofs/Sec6/Section6FromVolumeGrowth.lean:39-42` and `Section6FromLiterature.lean:47-50` each set `hW`
   by `lqgMeasureWeylScaling` internally. Their reductions take the volume-growth premise `hgrowth`
   (`LQGVolumeGrowthAllScalesStmt`, I2) together with `hAff`, `hCC` and `hE`. The exports here instead keep the Lemma 3.2,
   6.8, 6.10 and 6.13 leaves explicit. They are a different premise set, not duplicates.
2. Lemma 3.2 has a conditional provider `clusterOpenLaplacian_proved` (`HarmonicBalls/Proofs/Sec3/OpenLaplacian.lean:25`)
   from I2. It is not used here, because the task asks to expose the remaining derived leaves. The operator may choose
   to replace `h32` by I2.
3. `hex`: `lqgMeasureExistence_of_stronger` and `lqgMeasureExistence_of_cofinal`
   (`HarmonicBalls/Proofs/Sec6/WeakerSingularityExistence.lean:139,157`) are conditional. They need premises that this
   route does not have, so `hex` is kept as the staged premise.

## Guards (compiled in the same module)

* `#check` binders of the six declarations are printed in the `lc` log. The exports take the leaves in the order
  `hsub`, `hex`, `h32`, `h68`, `h610`, then `h613` (or `hdec`, `hdisc`), and conclude the named frozen Prop. The Weyl
  provider takes `Ω`, its instance, `P`, `γ`, `hC` and `hcirc`, and returns `LQGMeasureWeylScaling P γ 0 hC hcirc`.
* Meta guard (fail-closed): each export's type uses its frozen conclusion and its retained leaves; no export's type uses
  `HarmonicBalls.LQGMeasureWeylScaling`; each export and provider depends only on the three standard axioms; the provider's
  value applies `HarmonicBalls.Section6.lqgMeasureWeylScaling`.
* Combined import (scratch file in `/tmp` on the build host, not committed): the new module with
  `Proofs/Sec3/DerivedInputAssembly`, `Proofs/Sec4/DerivedInputAssembly`, `Proofs/Sec6/Section6FromVolumeGrowth`,
  `Proofs/Sec6/Section6LiteratureAssembly` and `Proofs/Sec6/AffineInvarianceAssembly`: CHECK OK. The root-level
  `HarmonicBalls.lqgMeasureWeylScaling_univ` (Sec3) and `HarmonicBalls.Section6Derived.lqgMeasureWeylScaling_univ`
  coexist; no name collision.
* Closure report, from the compile log: `LatticeProb` modules in the import closure of the module: 2.
  `LatticeProb` declarations reached by the exports: 0. Staged `HarmonicBalls.Proposed` modules reached: 1
  (`HarmonicBalls.Proposed.LQG`, through `hex` and the Weyl Prop).

## Bonanno credit

Two modules of Leonardo Bonanno's `LatticeProb` library lie in the import closure of the new module, through
`HarmonicBalls/Proofs/Sec6/Assembly.lean`. The header of the module credits him, with the annulus-iteration credit of
Lemma 6.5 recorded in `Section6FromVolumeGrowth.lean`. The constant closure of the exports reaches none of their
declarations, so these reductions use none of his results.

## Written argument

The new exports are the existing `harnackTypeComponentStmt_of_inputs` and `harnackTypeEstimateStmt_of_inputs`
(`Proofs/Sec6/Assembly.lean`) with `hW` instantiated. The written argument recorded there and in
`reports/c2.md` is unchanged. Its step for Lemma 6.3 uses `hW` (`reports/c2.md` line 10). This file does not re-derive
those steps, and it does not check them against the paper beyond the statements.

## Open items for the operator

* Open leaves remain explicit: `hsub`, `hex` (staged, source-check pending), `h32`, `h68`, `h610`, `h613` (or its steps).
  This is not a closure of Propositions 6.1 or 6.2.
* Option 2 above (replace `h32` by I2 through `clusterOpenLaplacian_proved`), if the operator wants fewer leaves.
* No STOP control, scheduled slot or other worker's file was touched.

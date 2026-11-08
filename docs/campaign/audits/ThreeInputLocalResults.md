# Lemmas 3.1-3.5, Proposition 4.1 and Lemmas 4.2-4.3 from the three staged measure inputs

Module: `HarmonicBalls/Proofs/Assembly/ThreeInputLocalResults.lean` (new, 267 lines). Worker z4, task `section3-section4-three-measure-input-assembly`. Credit: Leonardo Bonanno (module header). Scope: pure assembly and a conditional reduction. It is not numbered closure of any result below.

## Result

| export (module line) | frozen statement | premises |
|---|---|---|
| `leastSupersolutionMem_of_three_staged_inputs` (:83) | `LeastSupersolutionMemStmt`, Lemma 3.1 (`Draft/Section3.lean:47`) | `hDG`, `hCC`, `hE` |
| `clusterOpenLaplacian_of_three_staged_inputs` (:87) | `ClusterOpenLaplacianStmt`, Lemma 3.2 (`:66`) | `hDG`, `hCC`, `hE` |
| `clusterMonotone_of_three_staged_inputs` (:91) | `ClusterMonotoneStmt`, Lemma 3.3 (`:89`) | `hDG`, `hCC`, `hE` |
| `clusterConservationOfMass_of_three_staged_inputs` (:96) | `ClusterConservationOfMassStmt`, Lemma 3.4 (`:102`) | `hDG`, `hCC`, `hE` |
| `clusterCompatibility_of_three_staged_inputs` (:100) | `ClusterCompatibilityStmt`, Lemma 3.5 (`:119`) | `hDG`, `hCC`, `hE` |
| `clusterLowerBound_of_three_staged_inputs` (:104) | `ClusterLowerBoundStmt`, Proposition 4.1 (`Draft/Section4.lean:95`) | `hDG`, `hCC`, `hE` |
| `leastSupersolutionHolder_of_three_staged_inputs` (:108) | `LeastSupersolutionHolderStmt`, Lemma 4.2 (`:116`) | `hDG`, `hCC`, `hE` |
| `clusterSubharmonicBall_of_three_staged_inputs` (:112) | `ClusterSubharmonicBallStmt`, Lemma 4.3 (`:132`) | `hDG`, `hCC`, `hE` |

Typed examples at the frozen statements are at lines 116-123.

## Premises

Exactly three, in this order. All three are staged in `HarmonicBalls/Proposed/LQG.lean` and remain pending operator source-check. None is certified here.

- `hDG : WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:152`; Ding-Gwynne, Lemma 3.8).
- `hCC : LQGMeasureCoordChange P γ 0` (`Proposed/LQG.lean:114`; Fact 2.1 IV).
- `hE : LQGMeasureExistence P γ α` at every insertion `α : ℝ` (`Proposed/LQG.lean:66`; Section 2.2). The all-insertion quantifier is kept as written. It is the premise of `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`).

Not premises: the affine invariance (`wholePlaneGFFAffineInvariance_univ`, proved), nonatomicity (no binder), the Weyl scaling (no binder; not used by this route), and Input I2 (derived).

## Premise strength (not claimed equal, not claimed weaker)

The four-premise exports of `Proofs/Sec3/DerivedInputAssembly.lean` and `Proofs/Sec4/DerivedInputAssembly.lean` take `hE` at insertion `0` only, and `hN` (`LQGMeasureNonatomic`) at every insertion. The all-insertion `hE` here implies the insertion-`0` instance. Whether it also yields `hN` is part of the I2 derivation in `Proofs/Sec2/SingularAtomAtZero.lean:59`, which this file takes as written. The binder count alone does not show that the two premise sets are equivalent or that one is weaker.

## Derivation

1. I2 (`LQGVolumeGrowthAllScalesStmt`, `Draft/Section2.lean:122`) = `lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`), which is `lqgVolumeGrowthAllScalesStmt_of_stronger_singularity hDG wholePlaneGFFAffineInvariance_univ hCC hE` (`Proofs/Sec2/SingularAtomAtZero.lean:59`).
2. Each export is its `_proved` theorem applied to I2:
   - `leastSupersolutionMem_proved` (`Proofs/Sec3/Basic.lean:204`);
   - `clusterOpenLaplacian_proved` (`Proofs/Sec3/OpenLaplacian.lean:25`);
   - `clusterMonotone_proved` (`Proofs/Sec3/Basic.lean:209`);
   - `clusterConservationOfMass_proved` (`Proofs/Sec3/ConservationOfMassLemma.lean:30`);
   - `clusterCompatibility_proved` (`Proofs/Sec3/ClusterCompatibility.lean:360`);
   - `clusterLowerBound_proved` (`Proofs/Sec4/ClusterLowerBound.lean:18`);
   - `leastSupersolutionHolder_proved` (`Proofs/Sec4/LeastSupersolutionHolder.lean:19`);
   - `clusterSubharmonicBall_proved` (`Proofs/Sec4/ClusterGreenIdentity.lean:261`).

No new mathematics is added. The mathematics inside those theorems is taken as written in their modules.

## Guards

The guard is `#eval` code at the end of the module. It was run by `lc` and by the `lb` build.

- Printed axioms of all eight exports: `propext`, `Classical.choice`, `Quot.sound` only (`lc` log lines 1-12). The guard throws on any other axiom.
- Binder shape: exactly `hDG`, `hCC`, `hE`. Their domains equal, up to binder names, the premises of the staged I2 export. The head constants are `WholePlaneLQGBallMassBounds`, `LQGMeasureCoordChange`, `LQGMeasureExistence`. The `hE` domain has seven binders, the fifth named `α`. The conclusion is the frozen Stmt named in the table. Any other shape throws.
- Closure of the eight exports: 807 HarmonicBalls declarations (645 theorems) in 90 modules.
  - Proposed Props reached, all definitions: `WholePlaneGFFAffineInvariance`, `LQGMeasureWeylScaling`, `LQGMeasureNonatomic`, `LQGMeasureExistence`, `LQGMeasureCoordChange`, `WholePlaneLQGBallMassBounds`. Auxiliary obligation: `LQGMeasureExistence._proof_1`.
  - No Proposed or External theorem is reached.
  - LatticeProb declarations reached: 0.
- Forbidden, not reached: any theorem concluding `TypicalPointManyGoodScalesStmt` (open Lemma 8.2). No theorem concluding `SubharmonicBallUniquenessWeakStmt` (weak Prop 9.2, which needs `h82`) is reached.
- Section 4 declarations reached: 71. This is by design, since the three Section 4 exports consume the Section 4 proofs. Section 10 declarations reached: 0.

## Not claimed

- No numbered closure of Lemmas 3.1-3.5, Proposition 4.1 or Lemmas 4.2-4.3. Each export is a conditional reduction on `hDG`, `hCC` and `hE`.
- The Proposed inputs `hDG`, `hCC` and `hE` are unsourced until the operator source-checks them. Nothing in this module proves them.
- The mathematics of the `_proved` theorems and of the I2 route is not re-checked. This module checks the Lean composition, the binders and the constant closure.
- No frozen statement, existing export, staged input or Proposed or External declaration is edited.

## Build

- `lc HarmonicBalls/Proofs/Assembly/ThreeInputLocalResults.lean`: CHECK OK, log `/home/nitro/paper-fleets/hb/logs/lc/023852-1933929.log`.
- `lb HarmonicBalls.Proofs.Assembly.ThreeInputLocalResults`: BUILD OK, log `/home/nitro/paper-fleets/hb/logs/lb/023918-1935061.log`. 0 errors. No warning names this module.
- Code-level scan: no `sorry`, `admit`, `native_decide` or `set_option`. `axiom` occurs only in the `Lean.Util.CollectAxioms` import, the eight `#print axioms` lines and the guard.

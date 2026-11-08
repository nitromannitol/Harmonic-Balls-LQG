# Weak Proposition 9.2 from the staged measure inputs: I2 derived, affine invariance discharged, Lemma 8.2 kept open

Module: `HarmonicBalls/Proofs/Sec9/WeakUniquenessDerivedInputs.lean` (new). Worker z4, task `section9-weak-uniqueness-derived-volume-inputs`. Credit: Leonardo Bonanno (named in the module header and in both export docstrings). Scope: a reduction. It is not numbered closure of Proposition 9.2, Lemma 8.2, Input I1 or Input I2.

## Result

| export (module line) | frozen statement | premises |
|---|---|---|
| `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (:53) | `LQGVolumeGrowthAllScalesStmt`, Input I2 (`Draft/Section2.lean:122`) | `hDG`, `hCC`, `hE` |
| `subharmonicBallUniquenessWeak_of_stronger_singularity_typicalScales` (:66) | `SubharmonicBallUniquenessWeakStmt`, weak Prop 9.2 [C10] (`Draft/Section9.lean:125`) | `hDG`, `hCC`, `hE`, `h82` |

The premises are exactly these four:

- `hDG : WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:152`, Ding-Gwynne Lemma 3.8). Staged, pending operator source-check.
- `hCC : LQGMeasureCoordChange P γ 0` (`Proposed/LQG.lean:114`, Fact 2.1 IV). Staged, pending operator source-check.
- `hE : LQGMeasureExistence` at every insertion `α` (`Proposed/LQG.lean:66`). Staged, pending operator source-check. The body already requires `α₀ < lqgQ γ` (line 67), so the quantifier over all `α` adds no supercritical claim.
- `h82 : TypicalPointManyGoodScalesStmt` (`Draft/Section8.lean:74`, Lemma 8.2, `lemma:mu_h-doubling-and-harnack`). OPEN. It is the frozen binder and the derived proof obligation of this reduction. No Proposed or External Prop stands in for it.

## Derivation

1. `hAff` (`WholePlaneGFFAffineInvariance`) is `wholePlaneGFFAffineInvariance_univ` (`Proofs/Sec3/DerivedInputAssembly.lean:55`), the carrier-universal form of `wholePlaneGFFAffineInvariance_proved` (`Proofs/Sec9/AffineInvarianceAssembly.lean:21`). That proof applies `IsWholePlaneGFF.complex_affine` (`Proofs/Sec9/AffinePairingCovariance.lean:215`), which is a theorem. It is not a field of the structure (`Defs/GFF.lean:93`). So the invariance is derived from the covariance, not assumed in the definition of the field.
2. I2 = `lqgVolumeGrowthAllScalesStmt_of_stronger_singularity hDG wholePlaneGFFAffineInvariance_univ hCC hE` (`Proofs/Sec2/SingularAtomAtZero.lean:59`), whose written argument is the one in that file's header.
3. Weak Prop 9.2 = `subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales (I2) h82` (`Proofs/Sec9/AffineInvarianceAssembly.lean:30`).

## Guards

Checked by `lc` and by the `lb` build log of the module (the guard is `#eval` code at the end of the module):

- Printed axioms of both exports: `propext`, `Classical.choice`, `Quot.sound` only.
- Binder shape, read with `forallTelescope` from the constant's type: `hDG`, `hCC`, `hE`, `h82`, conclusion `SubharmonicBallUniquenessWeakStmt`. Any other shape throws.
- Closure of both exports: 1139 HarmonicBalls declarations (952 theorems) in 178 modules. Proposed Props reached, all definitions: `WholePlaneGFFAffineInvariance`, `LQGMeasureWeylScaling`, `LQGMeasureNonatomic`, `LQGMeasureExistence`, `LQGMeasureCoordChange`, `WholePlaneLQGBallMassBounds`. Auxiliary obligation: `LQGMeasureExistence._proof_1`. No Proposed or External theorem is reached. No `LatticeProb` declaration is reached (0 modules).
- Forbidden, and not reached: any theorem in `Proofs/Sec4/ClusterLowerBound`, `Proofs/Sec4/LeastSupersolutionHolder`, `Proofs/Sec4/ClusterGreenIdentity` or `Proofs/Sec4/DerivedInputAssembly`; any theorem concluding `ClusterLowerBoundStmt`, `LeastSupersolutionHolderStmt`, `ClusterSubharmonicBallStmt` or `TypicalPointManyGoodScalesStmt`. No reached theorem proves Lemma 8.2.
- I2 producers reached: six (`lqgVolumeGrowthAllScalesStmt_of_stronger_singularity`, `_of_literature`, `_of_DG`, `_of_rescaled`, `_of_scaled`, `_of_ballMass`). The reached theorems that take an I2 binder are listed in the log. Each is a conditional lemma whose I2 argument is built by a producer, not by a hypothesis of the exports.

## "Independent of Section4": what the closure shows

The numbered Section 4 results are not reached. The closure does reach Section 4 infrastructure through Section 6 lemmas, and Section 10 pole-avoiding lemmas through Section 6 annulus steps:

- `continuousOn_odometer` (`Steps/Sec4/Basic`), reached from `Section6.odometer_le_harmonicMeasure_of_local_generator_approximation`;
- `measurable_greenFunction` (`Proofs/Sec4/GreenAwayFromPole`), reached from `Section6.integrable_greenFunction_of_subset`;
- `odometer.eq_1`, reached from `Section6.harnack_core`;
- declarations of `Proofs/Sec4/GreenRepresentation`, and of `Proofs/Sec10/PoleAvoidingBoundarySup`, `PoleAvoidingGoodAnnulusDecay` and `PoleAvoidingTruncation`, reached through Section 6 entries such as `goodAnnulusOdometerDecayStep_of_volumeGrowth_and_harmonicMeasure`.

The full list (declaration and first parent) is in the `lc` log. Whether shared Section 4 and Section 10 infrastructure counts as dependence on Section 4 is for the operator to decide. The guard enforces the narrower rule above.

## Not claimed

- No closure of Proposition 9.2 (printed, strong or weak), Lemma 8.2, I1 or I2 as numbered results. This is a conditional reduction on `hDG`, `hCC`, `hE` and `h82`.
- The mathematics of `SingularAtomAtZero` (I2 from the four staged inputs) and of `subharmonicBallUniquenessWeak_of_dyadic_volumeGrowth` is taken as written in those files. This module checks the Lean composition, the binders and the closure.
- `wholePlaneGFFAffineInvariance_univ` is a proved Lean theorem. Its covariance route (`AffinePairingCovariance.lean:215`) is cited, not source-checked here.

## Build

- `lc HarmonicBalls/Proofs/Sec9/WeakUniquenessDerivedInputs.lean`: CHECK OK, log `logs/lc/013657-1811212.log`, 0 errors.
- `lb HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs`: BUILD OK, log `logs/lb/013724-1812454.log`, 0 errors. No warning names this module. The guard output in the build log matches the `lc` run.
- Code-level scan of the module: no `sorry`, `admit`, `native_decide` or `set_option`. The only `axiom` matches are the `CollectAxioms` import and the `#print axioms` and `collectAxioms` guard lines.

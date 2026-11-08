# Propositions 6.1 and 6.2 from the three staged inputs, with the open Section 6 leaves

Module: `HarmonicBalls/Proofs/Sec6/ThreeInputAssembly.lean` (new, 278 lines). Worker z4, task `section6-three-input-derived-laplacian-assembly`. Credit: Leonardo Bonanno (module header). Scope: pure assembly and a conditional reduction. It is not a closure of Proposition 6.1 or 6.2. Source review of the staged inputs is pending. No numbered closure is claimed.

## Result

| export (module line) | frozen statement | premises (binders, in order) |
|---|---|---|
| `harnackTypeEstimateStmt_of_three_inputs` (:72) | `HarnackTypeEstimateStmt`, Proposition 6.1 (`Draft/Section6.lean:206`) | `hDG`, `hCC`, `hE`, `hsub`, `h68`, `h610`, `h613` |
| `harnackTypeComponentStmt_of_three_inputs` (:91) | `HarnackTypeComponentStmt`, Proposition 6.2 (`:230`) | the same seven |
| `harnackTypeEstimateStmt_of_three_inputs_steps` (:109) | Proposition 6.1 | `hDG`, `hCC`, `hE`, `hsub`, `h68`, `h610`, `hdec`, `hdisc` |
| `harnackTypeComponentStmt_of_three_inputs_steps` (:127) | Proposition 6.2 | the same eight as the steps export |

Each proof is one application of `HarmonicBalls.Section6Derived` (`Proofs/Sec6/DerivedInputAssembly.lean`): `harnackTypeEstimateStmt_of_derived_weyl` (resp. `harnackTypeComponentStmt_of_derived_weyl`, and the `_steps` variants), with `hex := fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc` and `h32 := clusterOpenLaplacian_proved (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)`.

## Premises

Three staged measure inputs, at every carrier `Ω : Type u`. All are staged in `HarmonicBalls/Proposed/LQG.lean` and remain pending operator source-check. None is certified here.

- `hDG : WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:152`).
- `hCC : LQGMeasureCoordChange P γ 0` (`Proposed/LQG.lean:114`).
- `hE : LQGMeasureExistence P γ α` at every insertion `α : ℝ` (`Proposed/LQG.lean:66`). The all-insertion quantifier is kept as written. It is the third premise of `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`).

Open leaves, kept as explicit hypotheses (not derived here):

- `hsub : VeryGoodAnnuliSubRangeStep` (`Steps/Sec6/Prevalence.lean:54`).
- `h68 : AnnulusMassBoundByOdometerStmt` (Lemma 6.8, `Draft/Section6.lean:352`); `h610 : OdometerBoundByAnnulusMassStmt` (Lemma 6.10, `:388`); `h613 : LowMassSmallOdometerStmt` (Lemma 6.13, `:462`); or `hdec : GoodAnnulusOdometerDecayStep` (`Steps/Sec6/LowMass.lean:35`) and `hdisc : ComponentOdometerDiscMaxStep` (`:48`).

## Discharged inside the module (no binder)

- Weyl scaling `LQGMeasureWeylScaling` at insertion `0`: `Section6Derived.lqgMeasureWeylScaling_univ` (`Proofs/Sec6/DerivedInputAssembly.lean:49`), from `HarmonicBalls.Section6.lqgMeasureWeylScaling` (`Proofs/Sec6/LQGWeylScaling.lean:124`).
- Existence at insertion `0`: `hE` at `α = 0`.
- Affine invariance `WholePlaneGFFAffineInvariance`: inside I2, via `wholePlaneGFFAffineInvariance_univ` (`Proofs/Sec3/DerivedInputAssembly.lean:55`, proved).
- Lemma 3.2 `ClusterOpenLaplacianStmt`: `clusterOpenLaplacian_proved` (`Proofs/Sec3/OpenLaplacian.lean:25`) applied to I2. It is not re-exported: `clusterOpenLaplacian_of_three_staged_inputs` (`Proofs/Assembly/ThreeInputLocalResults.lean:87`, round 6) is the same Lemma 3.2 under the same three inputs.

## Comparison with the existing exports (no duplicate)

| route | premises | conclusion | Lemmas 6.8, 6.10, 6.13 and step hsub | LatticeProb reached |
|---|---|---|---|---|
| `section6_of_literature_without_weyl` (`Sec6/Section6FromLiterature.lean`) | `hDG`, `hAff`, `hCC`, `hE` (α = 0), `hN` | all 13 Section 6 statements | derived from volume growth | yes: it applies `section6_of_volumeGrowth` |
| `section6_of_volumeGrowth` (`Sec6/Section6FromVolumeGrowth.lean:21`) | `hgrowth`, `hAff`, `hCC`, `hE` (α = 0) | all 13 | 6.8, 6.10, 6.13 derived from volume growth; hsub not checked | yes (scratch check below) |
| this module | `hDG`, `hCC`, `hE` (all α), the leaves | Propositions 6.1 and 6.2 | assumed | none (guard) |

The exports here are not duplicates: they take neither `hAff` nor `hN`, and they take the leaves as hypotheses instead of deriving them.

## Finding for the operator

From `hDG`, `hCC` and `hE` alone, the existing chain `section6_of_volumeGrowth` applied to I2 (with `wholePlaneGFFAffineInvariance_univ`, `hCC`, and `hE` at `α = 0`) proves Propositions 6.1 and 6.2, together with the other eleven Section 6 statements. Scratch check, not committed: `/tmp/z4-compare/Compare.lean` on sandbox (copy in the z4 scratch area), `lc` CHECK OK, log `logs/lc/025133-1963968.log`. Its closure reaches 1979 HarmonicBalls declarations, 194 LatticeProb modules, among them `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6` (Bonanno's proof of the Gwynne–Miller lemma), and the annulus iteration `HarmonicBalls.Section6.annulusIterationStmt_proved`.

So the four leaves are open in this module only in the sense that the module does not use the LatticeProb route. Whether that route may close them is an operator decision. This module neither assumes nor claims it. Not checked: whether the volume-growth route reaches the step `VeryGoodAnnuliSubRangeStep` (hsub).

## Checks

- `lc`: CHECK OK on the final text, `logs/lc/025326-1967294.log`. An earlier run before the docstring edits, `logs/lc/025008-1961051.log`, gave the same guard output.
- `lb HarmonicBalls.Proofs.Sec6.ThreeInputAssembly`: BUILD OK, `logs/lb/025341-1967968.log`. 0 errors. No warning names the module; the 365 warnings in the log are replayed from other modules.
- Printed axioms of the four exports: `propext`, `Classical.choice`, `Quot.sound` only.
- Scan (`sorry`, `admit`, `native_decide`, `set_option`, the word `axiom`): no match in the module.
- Guard (`#eval` at the end of the module; output in the lb log): each export takes exactly `hDG hCC hE` followed by its leaves (binder names and premise heads checked). The `hDG`, `hCC` and `hE` domains equal those of I2. `hE` has seven binders with `α` fifth, so it quantifies over every insertion. The conclusions are the frozen Stmts. No affine, Weyl or Lemma 3.2 binder occurs.
- Closure of the four exports: 738 HarmonicBalls declarations (583 theorems) in 81 modules. The Proposed/External constants reached are definitions only: `LQGMeasureWeylScaling`, `WholePlaneGFFAffineInvariance`, `LQGMeasureNonatomic`, `LQGMeasureExistence`, `LQGMeasureCoordChange`, `WholePlaneLQGBallMassBounds`; auxiliary obligation `LQGMeasureExistence._proof_1`. LatticeProb modules reached: none. `annulusIterationStmt_proved` not reached. Section 4 and Section 10 declarations reached: 0.

## Not claimed and open

- No numbered closure. Propositions 6.1 and 6.2 are conditional on `hDG`, `hCC`, `hE` (source-check pending) and on the four leaves.
- No new literature input, no new Prop definition, no frozen definition or statement changed. `Defs`, `Draft`, `FROZEN`, `Proposed`, `External` and the paper are untouched, and no existing module was edited.
- Open leaves in this module: Lemmas 6.8, 6.10, 6.13 and the step `hsub`.

## Credit

Leonardo Bonanno (module header). Two LatticeProb modules, `LatticeProb.Prob.MaximalErgodic` and `LatticeProb.Prob.Birkhoff`, lie in the import closure through `Proofs/Sec6/LQGWeylScaling.lean`. The constant closure of these exports reaches no LatticeProb declaration. The volume-growth route reaches his Gwynne–Miller formalization `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.

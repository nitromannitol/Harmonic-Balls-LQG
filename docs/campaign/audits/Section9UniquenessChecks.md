# Section 9 uniqueness: current-export checks

2026-11-07 (worker z3). **Compilation of typed examples; conditional composition only.** The checks show that
the existing producers have the frozen types, at their explicit premises. No numbered result is closed here:
the premises in the table below remain open, and the printed strong Prop 9.2 has no producer.

Module: `HarmonicBalls/Audit/Section9UniquenessChecks.lean` (new). `lc` OK; `lb HarmonicBalls.Audit.Section9UniquenessChecks`
BUILD OK (`/home/nitro/paper-fleets/hb/logs/lb/002819-1652416.log`). It imports `HarmonicBalls.Proofs.Sec9.ObstacleComparison`,
`WeakUniqueness`, `DyadicGlobalUniqueness`, `AffineInvarianceAssembly`. Nothing was reproved: each example is an existing
declaration at its literal type, with its explicit premises as binders.

## Frozen targets (FROZEN.md; Draft/Section9.lean)

| Stmt | Result | Location |
|---|---|---|
| `ObstacleComparisonStmt` | Lemma 9.1 (`lemma:obstacle-comp`) | `Draft/Section9.lean:85` |
| `SubharmonicBallUniquenessWeakStmt` | Prop 9.2, weak form (E33(a)) | `Draft/Section9.lean:125` |
| `SubharmonicBallUniquenessStmt` | Prop 9.2, printed (PARTIAL) | `Draft/Section9.lean:109` (no producer; not claimed) |

## Producers and their explicit premises

| Declaration | Location | Explicit premises | Axioms |
|---|---|---|---|
| `obstacleComparison : ObstacleComparisonStmt` | `Proofs/Sec9/ObstacleComparison.lean:32` | none | standard |
| `IsSubharmonicBall.weak_uniqueness_of_volumeGrowth` (deterministic 9.2) | `Proofs/Sec9/SubharmonicSupersolution.lean:65` | local finiteness of `μ`; `IsSubharmonicBall μ A z`; `0<R`, `0<t`; `VolumeGrowth μ R βm βp`; `closure A ⊆ ball 0 R`; `μ A = ofReal t`; `IsOpen (cluster μ R z t)`; `μ (cluster μ R z t) = ofReal t` | standard |
| `subharmonicBallUniquenessWeak_of_boundaryNull` | `Proofs/Sec9/WeakUniqueness.lean:29` | `hI2`, `hboundary : ClusterBoundaryNullAllRadii` | standard |
| `clusterBoundaryNullAllRadii_of_dyadic_typical_scales` | `Proofs/Sec9/DyadicGlobalUniqueness.lean:48` | `hI2`, `h611` (Lemma 6.11), `h82` (Lemma 8.2), `hAff` | standard |
| `subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales` (top-level export) | `Proofs/Sec9/AffineInvarianceAssembly.lean:27` | `hI2`, `h82` | standard |
| `wholePlaneGFFAffineInvariance_proved` | `Proofs/Sec9/AffineInvarianceAssembly.lean:18` | none | standard |

The axiom sets came from the `lc` log of the module: each of the six `#print axioms` lines reports only
`propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, `admit`, `native_decide`, or project `axiom` occurs
(`grep "^axiom"` over `HarmonicBalls/` is empty).

## Chain for the frozen weak Prop 9.2

1. Lemma 9.1(1), deterministic form: `IsSubharmonicBall.greenPotential_le_of_steps` (`Steps/Sec9/ObstacleComparison.lean:45`)
   with `GreenFunctionBallSymmetric` (`:33`, proved by `greenFunction_ball_comm`, `Proofs/Potential/GreenBall.lean:296`) and
   `negGreenFunctionMemSubharmonicBallTestClass` (proved, `Proofs/Sec9/ObstacleComparison.lean`).
2. `IsSubharmonicBall.neg_greenPotential_mem_supersolutions` (`SubharmonicSupersolution.lean:11`) needs `VolumeGrowth`.
3. `cluster_subset_of_volumeGrowth` (`:54`) and `weak_uniqueness_of_volumeGrowth` (`:65`) give the deterministic conclusion.
4. Almost surely (`WeakUniqueness.lean`): volume growth at all radii from `ae_isLocallyFiniteMeasure_volumeGrowth hI2`;
   openness from `clusterOpenLaplacian_proved hI2` (Lemma 3.2, `Proofs/Sec3/OpenLaplacian.lean:25`); mass conservation from
   `clusterConservationOfMass_proved hI2` (Lemma 3.4, `Proofs/Sec3/ConservationOfMassLemma.lean:30`); and `hboundary`, the
   all-radii boundary-nullity step (`ClusterBoundaryNullAllRadii`, `WeakUniqueness.lean:20`).
5. Top level: `ClusterBoundaryNullAllRadii` comes from `clusterBoundaryNullAllRadii_of_dyadic_typical_scales`, which takes
   Lemma 8.2 (`h82`). Lemma 6.11 (`h611`) is derived inside the Section 6 chain from `hI2`
   (`subharmonicBallUniquenessWeak_of_dyadic_volumeGrowth`, `DyadicGlobalUniqueness.lean:35`), so it is not a premise of the export.

## Staged and derived predecessors (remaining premises)

| Predecessor | Location | Status |
|---|---|---|
| I2 `LQGVolumeGrowthAllScalesStmt` | `Draft/Section2.lean:122` (docstring 112-121: "a consequence, not a literature input", from Lemma 2.4 and scaling) | Explicit premise of the export. Two Lean producers, each conditional. (i) `lqgVolumeGrowthAllScalesStmt_of_ballMass` (`Steps/Sec2/VolumeGrowth.lean:164`) from `LiouvilleBallMassBoundStep` (`:69`), which `liouvilleBallMassBoundStep_of_scaled` (`Proofs/Sec2/BallMassReduction.lean:296`) derives from `WholePlaneScaledBallMassStep`, `SingularWeightStep`, `hE`, `hN`. (ii) `lqgVolumeGrowthAllScalesStmt_of_literature` (`Proofs/Sec2/Assembly.lean:120`) from the staged literature inputs `hDG` (Ding-Gwynne 2020, Lemma 3.8), `hAff`, `hCC`, `hW`, `hE`, `hN` (section variables, `Proofs/Sec2/Assembly.lean:61-73`). |
| Lemma 8.2 `TypicalPointManyGoodScalesStmt` | `Draft/Section8.lean:74` | Explicit premise of the export (through `clusterBoundaryNullAllRadii_of_dyadic_typical_scales`). Three Lean producers, each conditional. `typicalPointManyGoodScalesStmt_of_literature` (`Proofs/Sec8/TypicalPointLiteratureAssembly.lean:24`) from `hDG`, `hAff`, `hCC`, `hW`, `hEx` and the rooted and centred measure-law comparison `hcomparison`. `typicalPointManyGoodScalesStmt_of_ambientLaw` (`Proofs/Sec8/TypicalPointStatement.lean:19`) from `hgrowth` (I2), `hfull` (I1), `hsub` (`GoodAnnuliSubRangeStep`), `hEx`, `hW`, `hAff`, `hCC` and an explicit ambient-law comparison premise. `typicalPointManyGoodScalesStmt_of_staged_inputs_and_comparison` (`Proofs/Sec9/RootedComparisonWeakUniqueness.lean:57`) from `hDG`, `hCC`, `hE` and `hcomparison` (`:32`). |
| `WholePlaneGFFAffineInvariance` | `Proposed/LQG.lean:51` | Not a premise: proved from the covariance field `complex_affine` of `IsWholePlaneGFF` (`wholePlaneGFFAffineInvariance_proved`). Its definition sits in the Proposed file, so the operator's source-check of `IsWholePlaneGFF` covers it. |
| Lemma 6.11 `VeryGoodAnnulusHarnackTypeStmt` | `Draft/Section6.lean:415` | Not a premise of the top-level export: derived from `hI2` in the Section 6 chain. |
| Lemma 3.2, Lemma 3.4 | `Proofs/Sec3/OpenLaplacian.lean:25`, `Proofs/Sec3/ConservationOfMassLemma.lean:30` | Proved from `hI2` alone. |
| `ClusterBoundaryNullAllRadii` | `Proofs/Sec9/WeakUniqueness.lean:20` | Proof step (its docstring says it is not a literature input). It is a premise of `subharmonicBallUniquenessWeak_of_boundaryNull` and is discharged by `h82` through its producer. |

Remaining premises for the frozen weak Prop 9.2 export: **I2 and Lemma 8.2 as explicit binders, and nothing else**
(the typed examples compile with exactly these two). Neither is discharged unconditionally here: their Lean producers take the
staged items named above (`hDG`, `hAff`, `hCC`, `hW`, `hE`, `hN`, `hEx`, `hcomparison`, `WholePlaneScaledBallMassStep`,
`SingularWeightStep`, `GoodAnnuliSubRangeStep`, and an ambient-law comparison), all pending operator source-check or
rooted-law work.

## What this audit does not claim

* Not closure of Lemma 9.1, Prop 9.2 (weak or printed), Lemma 9.3, Lemma 9.4, or Prop 5.6. I2 and Lemma 8.2 stay explicit,
  and the staged items above are not source-checked here.
* The printed `SubharmonicBallUniquenessStmt` has no producer. Its first conclusion needs `int(closure Λ) ⊆ A`, which the proof
  does not show (ESCALATIONS E11, `docs/campaign/GRAPH.md` F5, E33(a)). It is not audited as closed.
* The frozen Lemma 9.1 Stmt is quantified over LQG realisations, so it cannot be instantiated at an arbitrary measure. It has no
  downstream Lean consumer. The uniqueness chain uses the deterministic `greenPotential_le_of_steps`, which holds for every measure.
  The export therefore does not go through the frozen Lemma 9.1 Stmt.

## Observations for the operator

1. `Steps/Sec9/ObstacleComparison.lean:32` labels `GreenFunctionBallSymmetric` "input I4". The Proofs file proves it with
   `greenFunction_ball_comm`, so the label is stale. No mathematical gap.
2. Correction to the earlier planning note (`docs/campaign/audits/Section9ComparisonExports.md`, "8.2 is unproved"): Lemma 8.2
   and I2 do have Lean producers, as listed above. They are conditional on the staged items, so "unproved" means the
   conditional status, not the absence of a producer.
3. Existing coverage, not re-checked here: `Audit/Section9ComparisonExports.lean` covers the top-level weak 9.2 export, 9.3 and 9.4;
   `Audit/Section5ExistenceUniqueness.lean` covers Prop 5.6.

## Credit

The imported Section 6 and Section 8 proofs use Leonardo Bonanno's `LatticeProb.Bonanno` development and `LatticeProb.Prob.Birkhoff`
(the import closure of the new module, 511 HarmonicBalls modules, reaches `Proofs/Sec6/AnnulusIteration.lean`,
`Proofs/Sec8/BirkhoffPort.lean`, and the Bonanno field modules). The new module carries the same credit in its docstring.

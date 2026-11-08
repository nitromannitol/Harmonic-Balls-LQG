# Section 3 derived-input assembly: five exports at the frozen statements

TASK: section3-discharge-derived-affine-weyl-inputs (worker z4, Claude Haiku 5.5, 2026-11-07). Lean file: `HarmonicBalls/Proofs/Sec3/DerivedInputAssembly.lean` (new).
Scope: Lemmas 3.1-3.5 at their frozen statements, with the affine and Weyl premises discharged by their existing proofs. Lean only: no new mathematics, no numbered closure, no edit to the old six-premise assembly, to frozen statements, to `Proposed`, `External` or the paper.

## Result

The five exports compile at their frozen types with exactly four hypotheses: the staged Props `WholePlaneLQGBallMassBounds`, `LQGMeasureCoordChange`, `LQGMeasureExistence` and `LQGMeasureNonatomic`. Every printed axiom set is `[propext, Classical.choice, Quot.sound]`.

| Lemma | Frozen statement (`Draft/Section3.lean`) | New export (`DerivedInputAssembly.lean`) | Existing export applied (`Proofs/Sec3/Assembly.lean`) |
|---|---|---|---|
| 3.1 `lemma:basic-properties` | `LeastSupersolutionMemStmt` (:47) | `leastSupersolutionMem_of_remaining_literature` (:70) | `leastSupersolutionMem_of_literature` (:40) |
| 3.2 `lemma:non-coincidence-open-harmonic` | `ClusterOpenLaplacianStmt` (:66) | `clusterOpenLaplacian_of_remaining_literature` (:74) | `clusterOpenLaplacian_of_literature` (:44) |
| 3.3 `lemma:monotonicity` | `ClusterMonotoneStmt` (:89) | `clusterMonotone_of_remaining_literature` (:78) | `clusterMonotone_of_literature` (:48) |
| 3.4 `lemma:conservation-of-mass` (C4) | `ClusterConservationOfMassStmt` (:102) | `clusterConservationOfMass_of_remaining_literature` (:82) | `clusterConservationOfMass_of_literature` (:52) |
| 3.5 `lemma:cluster-compatibility` | `ClusterCompatibilityStmt` (:119) | `clusterCompatibility_of_remaining_literature` (:86) | `clusterCompatibility_of_literature` (:56) |

Each new export is the existing export applied to `hDG`, `wholePlaneGFFAffineInvariance_univ`, `hCC`, `lqgMeasureWeylScaling_univ`, `hE`, `hN`. No existing export or frozen statement is edited.

## Derived premises (no hypothesis)

| Premise | Universal provider (new, `Type u`) | Proved provider | Prop (`Proposed/LQG.lean`) |
|---|---|---|---|
| `hAff` | `wholePlaneGFFAffineInvariance_univ` (:55) | `wholePlaneGFFAffineInvariance_proved` (`Proofs/Sec9/AffineInvarianceAssembly.lean:18`) | `WholePlaneGFFAffineInvariance` (:51) |
| `hW` | `lqgMeasureWeylScaling_univ` (:62), `α₀ = 0` | `HarmonicBalls.Section6.lqgMeasureWeylScaling` (`Proofs/Sec6/LQGWeylScaling.lean:121`) | `LQGMeasureWeylScaling` (:93) |

Both providers are stated for every `Ω : Type u` and take no hypothesis beyond the carrier, measure and fields of the Prop.

## Retained explicit hypotheses (four staged Props; not proved, not certified)

| Hypothesis | Prop (`Proposed/LQG.lean`) | Source as cited in the Prop's docstring |
|---|---|---|
| `hDG` | `WholePlaneLQGBallMassBounds` (:152) | Ding-Gwynne 2020, Lemma 3.8 (as cited in `Proofs/Sec3/Assembly.lean`) |
| `hCC` | `LQGMeasureCoordChange` (:114) | Fact 2.1 IV, conformal covariance (eq:measure-coord) |
| `hE` | `LQGMeasureExistence` (:66) | Bou-Rabee-Gwynne, Section 2.2, p. 9 |
| `hN` | `LQGMeasureNonatomic` (:75) | Fact 2.1 I, non-atomicity |

These four stay pending operator source-check. This audit neither proves them nor source-admits them.

## Checks

Log of the final `lc` run: `logs/lc/005510-1724997.log`; `lb` build: `logs/lb/005517-1725350.log`.

- Printed axioms: seven declarations (the two providers and the five exports), each `[propext, Classical.choice, Quot.sound]`.
- Typed examples: five `example`s at the exact frozen statements, each with the four retained premises as the only hypotheses; the `#check` lines print the five signatures.
- Guards (compile-time, fail-closed, at the end of the file):
  1. each export's type mentions the four retained premises and none of `WholePlaneGFFAffineInvariance`, `LQGMeasureWeylScaling`, `LQGVolumeGrowthAllScalesStmt` (input I2 is produced inside `lqgVolumeGrowthAllScalesStmt_of_literature`, so it is not a hypothesis);
  2. each export's value applies both universal providers;
  3. the constant closure of the two providers reaches 110 HarmonicBalls declarations, none in `Proofs/Sec2/Assembly`, `Proofs/Sec3`, `Steps/Sec3`, `Proofs/Sec4` or `Steps/Sec4`, and no theorem or opaque constant of `Proposed` or `External`.
- Closure details: the two `Proposed` definitions reached are the two Props in the providers' types. One auxiliary is reached, `HarmonicBalls.LQGMeasureExistence._proof_1 : (1 + 1).AtLeastTwo`, a numeral-instance proof for the `2` in `γ < 2` that depends on `propext` only (checked by a probe file outside the repository).
- Code scan of the new file: no `sorry`, `admit`, `native_decide`, `axiom` declaration, `set_option maxHeartbeats`, `unsafe`, `implemented_by` or `extern`.
- `lb` log: the thirteen messages attributed to the new file are `info` lines (five `#check`, seven `#print axioms`, one guard summary); no warning or error is attributed to it.

## Import inspection (circularity)

- `grep -rln DerivedInputAssembly HarmonicBalls docs lakefile.lean` finds only the new file. No module imports it, so neither provider can depend on it.
- Import closures (probe files, `lc`): `Proofs/Sec3/Assembly.lean` has no LatticeProb module; `Proofs/Sec6/LQGWeylScaling.lean` has 2; `Proofs/Sec9/AffineInvarianceAssembly.lean` has 303. Neither provider's constant closure reaches a LatticeProb declaration.

## Attribution

- Leonardo Bonanno is credited in the module docstring. The LatticeProb library of Leonardo Bonanno is in the import closure of the new file, through `Proofs/Sec9/AffineInvarianceAssembly.lean`. The constant closure of the five exports contains no declaration of that library: the two providers reach none, and the Section 3 assembly's import closure contains none of its modules.
- Gap for the operator (not owned by this task, not edited): `Proofs/Sec9/AffineInvarianceAssembly.lean` and `Proofs/Sec6/LQGWeylScaling.lean` import LatticeProb modules and do not name Bonanno (no hit for `Bonanno` in either file). The repository names him in 683 files, so these two files may need the same line.

## Open

- The four retained Props stay hypotheses, so the five exports are closed only relative to them. No numbered closure is claimed.
- Task overlap: `tasks/c1.md` claims `HarmonicBalls/Proofs/Sec3/*` by wildcard. This task names `DerivedInputAssembly.lean` explicitly, and no other task should edit it.

# Section 5 input consumption check

Task `section5-volume-input-consumption-check` (worker z4, round 9). Scope: the frozen statements of Section 5
(`HarmonicBalls/Draft/Section5.lean:122,140,155,175,192,206,226,246`; FROZEN.md:42-49) and their producers in
`Steps/Sec5`, `Proofs/Sec5`, `Proofs/Sec7`-`Sec9`. Owned output: `HarmonicBalls/Audit/Section5InputChecks.lean` (new).
No source-facing edit, no literature input, no numbered closure. Draft, FROZEN, Proposed and the paper are unchanged.

## Validation

- `lc HarmonicBalls/Audit/Section5InputChecks.lean`: CHECK OK (log 033528-2049218).
- `lb HarmonicBalls.Audit.Section5InputChecks`: BUILD OK (log 033535-2049809).
- Printed axioms of the 11 exports: `propext`, `Classical.choice`, `Quot.sound` only.
- Code-level scan of the owned Lean file for `sorry`, `admit`, `native_decide`, `axiom`: no match.

## Typed exports and classification

Each row is a Lean theorem whose only hypotheses are the listed binders. The binder list is the check: a missing
binder would fail to typecheck, and an extra one would appear in the signature.

| Result (paper) | Frozen Stmt | Audit export (Audit/Section5InputChecks.lean) | Binders beyond I2 | Classification |
|---|---|---|---|---|
| 5.1 prop:upper-bound | `ClusterUpperBoundStmt` | `section5_clusterUpperBound_of_I2` | Lemma 2.4, Prop 6.1 | conditional on I2, 2.4, 6.1 |
| 5.2 prop:continuity | `ClusterContinuityStmt` | `section5_clusterContinuity_of_I2` | 2.4, 6.1, Lemma 8.2, `ClusterBoundaryTouchingRightContinuityStep` | OPEN: last binder has no producer (G12) |
| 5.3 prop:boundary-measure | `ClusterBoundaryMeasureZeroStmt` | `section5_clusterBoundaryMeasureZero_of_I2` | Lemma 8.2 | conditional on I2 and the open 8.2 |
| 5.4 prop:conditional | `RegularizedClusterHarmonicBallsStmt` | `section5_regularizedCluster_of_I2` | 2.4, 6.1, Lemma 8.2 | conditional on I2, 2.4, 6.1, open 8.2 |
| 5.5 theorem:full-theorem-minus-uniqueness | `ExistenceHarmonicBallsStmt` | `section5_existence_of_I2` | 2.4, 6.1, Lemma 8.2, `hCC` at all insertions | conditional on I2 and the leaves above |
| 5.6 prop:uniqueness | `UniquenessHarmonicBallsStmt` | `section5_uniqueness_of_I2` | none | conditional on I2 only; E51 open |
| 5.7 lemma:scale-invariance-flow | `ClusterScaleInvarianceStmt` | `section5_clusterScaleInvariance_of_I2` | `hCC` at all insertions | conditional on I2 and `hCC` (Proposed) |
| 5.8 lemma:strong-compatibility | `ClusterStrongCompatibilityStmt` | `section5_clusterStrongCompatibility_of_I2` | none | conditional on I2 only; G9/E51 semantics open |

No numbered result 5.1-5.8 is unconditional in the repository. 5.6 and 5.8 are the only exports that need no
binder beyond I2. Consumption from the staged Proposed inputs is typed as well, for 5.6 and 5.8:
`section5_uniqueness_of_staged_inputs` and `section5_clusterStrongCompatibility_of_staged_inputs` take `hDG`, `hCC`
(insertion `0`) and `hE`.

## Leaf table

| Leaf (exact Prop) | Status | Provider or source (file:line) |
|---|---|---|
| I2 `LQGVolumeGrowthAllScalesStmt` (Draft/Section2.lean:122) | consumed; conditional on the three staged inputs | `section5_volumeGrowth_of_staged_inputs` wraps `lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53-57) |
| staged `hDG` `WholePlaneLQGBallMassBounds` | Proposed, pending source check | Proposed/LQG.lean:152 |
| staged `hCC` `LQGMeasureCoordChange P γ 0` | Proposed, pending source check; insertion `0` only | Proposed/LQG.lean:114 |
| staged `hE` `LQGMeasureExistence` | Proposed, pending source check | Proposed/LQG.lean:66 |
| all-insertion `hCC` `LQGMeasureCoordChange P γ α₀` | Proposed binder for 5.5 and 5.7; not provided by the staged I2 (type mismatch: insertion `0` only) | Proposed/LQG.lean:114 |
| I1 `LQGMeasureFullSupportStmt` (Draft/Section2.lean:109) | derived from I2, no binder | `lqgMeasureFullSupportStmt_of_volumeGrowth` (Steps/Sec2/VolumeGrowth.lean:220) |
| affine invariance `WholePlaneGFFAffineInvariance` | proved, no binder | `wholePlaneGFFAffineInvariance_proved` (Proofs/Sec9/AffineInvarianceAssembly.lean:21) |
| Lemma 3.2 / 3.3 / 3.4 | derived from I2, no binder | `clusterOpenLaplacian_proved` (Proofs/Sec3/OpenLaplacian.lean:25), `clusterMonotone_proved` (Proofs/Sec3/Basic.lean:209), `clusterConservationOfMass_proved` (Proofs/Sec3/ConservationOfMassLemma.lean:30) |
| Lemma 6.11 `VeryGoodAnnulusHarnackTypeStmt` (Draft/Section6.lean:415) | derived from I2, no binder | `Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only` (Proofs/Sec6/VolumeGrowthConsequences.lean:19) |
| Lemma 9.3 / 9.4 | derived from I2, no binder | `harmonicBallBoundarySubset_of_volumeGrowth` (Proofs/Sec9/HarmonicBoundaryAssembly.lean:19), `regularOpenEqOfAEEq_of_volumeGrowth` (Proofs/Sec9/VolumeGrowthAssembly.lean:11) |
| Lemma 8.1 `BoundaryMeasureZeroOfCompactClusterStmt` (Draft/Section8.lean:55) | derived from 3.2, 6.11, 8.2 | `boundaryMeasureZeroOfCompactClusterStmt_of_steps` (Proofs/Sec8/ClusterBoundary.lean:89) |
| Lemma 2.4 `LiouvilleVolumeGrowthStmt` (Draft/Section2.lean:89) | binder, leaf | providers `liouvilleVolumeGrowthStmt_of_DG` (Proofs/Sec2/Assembly.lean:80, takes hDG, hAff, hCC, hMix, hW, hE, hN) and `_of_literature` (:116); no I2-only provider found |
| Prop 6.1 `HarnackTypeEstimateStmt` (Draft/Section6.lean:206) | binder, leaf | `harnackTypeEstimateStmt_of_three_inputs` (Proofs/Sec6/FullThreeInputAssembly.lean:56, hDG hCC hE; Section 6 task, not consumed here); `harnackTypeEstimateStmt_of_volumeGrowth` (Proofs/Sec6/VolumeGrowthAssembly.lean:70, extra binders hsub, hex, hW, hdec) |
| Lemma 8.2 `TypicalPointManyGoodScalesStmt` (Draft/Section8.lean:74) | OPEN | providers take hDG, hCC, hE and the proof obligation `hcomparison` (Proofs/Sec9/RootedComparisonWeakUniqueness.lean:34-52, include at :53; Proofs/Sec8/TypicalPointStatement.lean:34). The module doc (TypicalPointStatement.lean:4-7) says the comparison hypothesis is a proof obligation, not an external literature input. |
| step `ClusterBoundaryTouchingRightContinuityStep` (Steps/Sec5/ContinuityAssembly.lean:19-26) | OPEN, no producer | right continuity at times with `closure (cluster ..)` not in B1; G12 (docs/campaign/GRAPH.md:1352): Prop 7.2 needs `Λ ⋐ B1` |

## Reciprocity, bounded representatives, regular boundary

- No export above has a reciprocity, bounded-representative or regular-boundary binder. No `Prop` named
  `...Reciprocity...` exists in Steps, Proofs, Assembly, Proposed, Defs or Draft. `HasBoundedSubharmonicRepresentatives`
  occurs only in `Proofs/Potential/BoundedSubharmonicRepresentatives.lean`, so no Section 5 export uses it.
- Bounded-domain Green reciprocity is blocked: `docs/campaign/audits/BoundedDomainGreenReciprocity.md:1-4` says no
  general reciprocity has been proved. Bounded subharmonic representatives are "neither proved nor refuted"
  (`docs/campaign/audits/BoundedSubharmonicRepresentatives.md`). The exports above do not depend on either at binder level.
- Regular boundary: `clusterStrongCompatibilityStmt_of_volumeGrowth` (Proofs/Sec5/StrongCompatibilityAssembly.lean:15)
  uses the proved Green-regular exhaustion (`exists_greenRegular_exhaustion`, Proofs/Potential/GreenRegularDomainExhaustion.lean).
  Its Lean statement covers every bounded open `U`, so the irregular-boundary question is semantic (E51, G9), not a binder.

## E51 routing (semantic; no Lean edit)

Exact evidence for the Green and test-class mismatch:

1. `HarmonicBalls/Draft/Section4.lean:57-69`, `subharmonicBallTestClass (Λ) (z)`: the body is
   `{f | ∃ (O K : Set ℂ) (ν₁ ν₂ : Measure ℂ) (q : ℂ → ℝ), IsOpen O ∧ closure Λ ⊆ O ∧ ...}`. The binder `O` carries only
   `IsOpen O`, with no boundedness and no Greenian condition.
2. `HarmonicBalls/Defs/Green.lean:28-31` (docstring): the paper uses only bounded `O`; for a non-Greenian `O` such as
   `ℂ` the greatest harmonic minorant is `⊥` and the value is junk.
3. `HarmonicBalls/Defs/Green.lean:70-74`, `greenFunction O x y`: `if x ∈ O ∧ y ∈ O ∧ x ≠ y then newtonKernel x y -
   (greatestHarmonicMinorant O (newtonKernelEReal x) y).toReal else 0`.
4. `HarmonicBalls/Draft/Section5.lean:103-107`, `supersolutionsOn μ U z t`: `ContinuousOn w (closure U) ∧
   LaplacianLE w μ U ∧ ∀ x ∈ closure U, x ≠ z → -t * greenFunction U z x ≤ w x`. Its docstring records the G9
   ambiguity at irregular boundary points. `clusterOn` (:114-116) is built from the same `greenFunction U z`.
5. `HarmonicBalls/Draft/Section5.lean:246-257`, `ClusterStrongCompatibilityStmt`: `∀ U : Set ℂ, IsOpen U →
   Bornology.IsBounded U → ...`, so the statement quantifies over every bounded open `U`.

Routing: E51 (Green/test-class equivalence) and G9 (irregular domains) remain fail-closed. 5.8 is a Lean-literal
theorem; its statement for irregular `U` is not certified. 5.6 is stated for `IsHarmonicBallFamily`
(Draft/Section1.lean:82) and its enlarged test class, which the Prop 5.6 docstring (Draft/Section5.lean:198-205) ties to
the subharmonic-ball test class. `Section5ExistenceUniqueness.md` records the same non-Greenian semantics failure for
this chain. Operator decision needed; no Draft edit.

## Open items for the operator

1. `ClusterBoundaryTouchingRightContinuityStep` (Steps/Sec5/ContinuityAssembly.lean:19) has no producer. 5.2 cannot
   be closed from the repository. This is the G12 scope gap.
2. `TypicalPointManyGoodScalesStmt` (Lemma 8.2) is open through `hcomparison` (RootedComparisonWeakUniqueness.lean:34-52).
   It blocks 5.3 directly and 5.2, 5.4, 5.5 through Lemma 8.1 and Proposition 7.2.
3. Lemma 2.4 and Proposition 6.1 are leaves with providers that need Section 2 and Section 6 inputs. They are not consumed here.
4. The all-insertion `LQGMeasureCoordChange` (Proposed/LQG.lean:114) is needed for 5.5 and 5.7. The staged I2 provider takes insertion `0` only.
5. E51 and G9 as routed above.

## Credit

Leonardo Bonanno's potential-theoretic and LatticeProb work is consumed through the imported modules. The module
docstring names Leonardo Bonanno, and so do the credited modules (for example `Proofs/Potential/FiniteDiscGreenReciprocity.lean`
and `Proofs/Sec8/TypicalPointStatement.lean`, which credits the `LatticeProb.Prob.Birkhoff` formalization).

# Section 3 input consumption checks

TASK: z4-sec3-input-consumption-check (worker z4, 2026-11-07). Lean file: `archive/HarmonicBalls/Audit/Section3InputChecks.lean`.
Scope: type-check of the existing exports of Lemmas 3.1-3.5 against the frozen statements. Lean only, no new mathematics,
no source admission of any literature input, not closure of Section 3.

## Result

The five exports of `HarmonicBalls/Proofs/Sec3/Assembly.lean` have the frozen statements of `HarmonicBalls/Draft/Section3.lean`.
The audit file restates each as a typed `example` with the six staged literature premises explicit, in universe `u`:

| Result | Frozen statement (Draft/Section3.lean) | Export (Proofs/Sec3/Assembly.lean) | Applied `_proved` lemma |
|---|---|---|---|
| Lemma 3.1 (lemma:basic-properties) | `LeastSupersolutionMemStmt` :47 | `leastSupersolutionMem_of_literature` | `leastSupersolutionMem_proved` (Proofs/Sec3/Basic.lean:204) |
| Lemma 3.2 (lemma:non-coincidence-open-harmonic) | `ClusterOpenLaplacianStmt` :66 | `clusterOpenLaplacian_of_literature` | `clusterOpenLaplacian_proved` (Proofs/Sec3/OpenLaplacian.lean:25) |
| Lemma 3.3 (lemma:monotonicity) | `ClusterMonotoneStmt` :89 | `clusterMonotone_of_literature` | `clusterMonotone_proved` (Proofs/Sec3/Basic.lean:209) |
| Lemma 3.4 (lemma:conservation-of-mass) | `ClusterConservationOfMassStmt` :102 | `clusterConservationOfMass_of_literature` | `clusterConservationOfMass_proved` (Proofs/Sec3/ConservationOfMassLemma.lean:30) |
| Lemma 3.5 (lemma:cluster-compatibility) | `ClusterCompatibilityStmt` :119 | `clusterCompatibility_of_literature` | `clusterCompatibility_proved` (Proofs/Sec3/ClusterCompatibility.lean:360) |

Each export is `<result>_proved (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN)`.

## Premises that remain (explicit; pending operator source-check; `HarmonicBalls/Proposed/LQG.lean`)

- `hDG`: `WholePlaneLQGBallMassBounds` (:152); Ding-Gwynne 2020 Lemma 3.8 (docs/campaign/FROZEN.md:95).
- `hAff`: `WholePlaneGFFAffineInvariance` (:51).
- `hCC`: `LQGMeasureCoordChange` (:114); `hW`: `LQGMeasureWeylScaling` (:93); `hE`: `LQGMeasureExistence` (:66);
  `hN`: `LQGMeasureNonatomic` (:75). The Assembly header cites these four as Fact 2.1.

No other premise is used. `IsWholePlaneGFF` and `IsLQGMeasureOfField` are definitions, not literature inputs.

## I2 consumption

I2 is `LQGVolumeGrowthAllScalesStmt` (Draft/Section2.lean:122; FROZEN.md:24), a derived input. No export takes it as a
hypothesis. The `_proved` lemmas take it as `hI2`, and each export instantiates it with
`lqgVolumeGrowthAllScalesStmt_of_literature` (Proofs/Sec2/Assembly.lean:120, worker c2), which consumes the six premises
above. The Lean guard checks that the export's type does not mention I2 and that the export's value applies this producer.

## Axioms

`#print axioms` on the five exports gives `[propext, Classical.choice, Quot.sound]` for each. The guard checks this in Lean.
The file has no `sorry`, `admit`, `native_decide`, `set_option maxHeartbeats` or `axiom` declaration.

## Circularity

1. Import level. A bash BFS over `^import` lines:
   - `HarmonicBalls.Proofs.Sec2.Assembly` (the I2 producer) reaches 23 repo modules: Proofs.Sec2 (12), Steps.Sec2, Draft.Section2,
     Proposed.LQG and Defs (8). It reaches no Section 3 or Section 4 module. External roots: MarkovProcess and Mathlib only.
   - `HarmonicBalls.Proofs.Sec3.Assembly` reaches 60 repo modules, including Proofs.Sec2, Proofs.Sec3 (9), Steps.Sec3 (7),
     Draft.Section3 and Proposed.LQG. No LatticeProb module is reached.
   The producer's closure contains no Section 3 module, so there is no import cycle.
2. Constant level (guard in the audit file). The closure of `lqgVolumeGrowthAllScalesStmt_of_literature` through HarmonicBalls
   declarations, followed through types and values, reaches 178 declarations. None lies in `Proofs.Sec3`, `Steps.Sec3`,
   `Draft.Section3`, `Proofs.Sec4`, `Steps.Sec4` or `Draft.Section4`. Negative control: the same guard with
   `HarmonicBalls.Proofs.Sec2` added to the forbidden list fails at the producer, so the traversal is not vacuous
   (`/tmp/z4-negctl/NegControl.lean`, outside the repo; `error: ... circular dependency`).
3. Source level (corrected draft). The appendix hypothesis `eq:volume-growth` (`paper/lqg_harmonic_ball-corrected.tex:4041`) is I2's
   statement. Its printed derivation is one sentence (tex:4044): "this follows from Lemma~\ref{lemma:volume-growth} and the scaling
   properties of $h$ and $\mu_h$, namely~\eqref{eq:h-coordinate-change} and~\eqref{eq:measure-coord}". Lemma 2.4
   (`lemma:volume-growth`, tex:501) is a Section 2 result, cited to Berestycki-Gwynne 2020 (docs/campaign/INVENTORY.tsv, row 2.4).
   Neither cites a Section 3 result. Section 3 consumes I2 through Appendix A (Lemma A.6, `lemma:appendix-cluster-compatibility`
   takes eq:volume-growth on B_R as input); GRAPH.md:87-88 lists I2 as used by App A, Prop 2.5 and Lemma 4.2.
   No circular source dependency was found.

Conclusion: I2 is consumed through its producer, and no source or target dependency between I2 and Lemmas 3.1-3.5 is circular.

## Gaps and notes for the operator (not closed here)

- G-A (source, terse derivation). The printed sentence at tex:4044 omits the step that GRAPH.md:87-88 says is needed:
  Borel-Cantelli over dyadic scales and monotonicity in r, for all centres z in B_R. The Lean counterpart is in
  `HarmonicBalls/Steps/Sec2/VolumeGrowth.lean:162` (Borel-Cantelli from `LiouvilleBallMassBoundStep`). That file belongs to the
  Section 2 audit and is not re-checked here.
- G-B. Every result above is conditional on the six literature Props in Proposed/LQG.lean, which await operator source-check.
  Compilation is not numbered-result closure.
- Bonanno. No LatticeProb.Bonanno module is imported by the audit file (checked by the guard), so no Bonanno credit line is required.

## Build

- lc: `CHECK OK` on `archive/HarmonicBalls/Audit/Section3InputChecks.lean` (log: /home/nitro/paper-fleets/hb/logs/lc/002927-1659277.log).
- lb: `BUILD OK (HarmonicBalls.Audit.Section3InputChecks)` (log: /home/nitro/paper-fleets/hb/logs/lb/002936-1659497.log).
- The `#print axioms` lines and the guard message are in the lc log of the earlier run (002732-1650530.log); the final edit touched only a docstring.

# Section 4 input consumption checks: Proposition 4.1 and Lemmas 4.2-4.3

TASK: z3-section4-input-consumption-check (worker z3, Claude Haiku 5.5, 2026-11-07). Lean file:
`archive/HarmonicBalls/Audit/Section4InputChecks.lean` (new). Lean only. No frozen statement, staged premise or existing export
is edited, and no numbered result is closed by this file.

## Result

* `lc archive/HarmonicBalls/Audit/Section4InputChecks.lean`: CHECK OK. `lb HarmonicBalls.Audit.Section4InputChecks`: BUILD OK.
  The module emits no warning or error; its log lines are the printed axioms and the guard summary.
* Printed axioms: all nine constants (the six exports, the I2 producer and the two derived providers) depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
* Forbidden-token scan (`sorry`, `admit`, `native_decide`, `opaque`, `unsafe`, `implemented_by`, `extern`, `set_option`,
  and `axiom` declarations) on the new file: no match.
* Each of the three numbered results has three export routes. All are type-checked at the frozen statements of
  `HarmonicBalls/Draft/Section4.lean` (lines 95, 116, 132; FROZEN.md entries 39-41):

| result (frozen Stmt) | literature route, six premises | derived route, four premises | proof route, I2 only |
|---|---|---|---|
| Prop 4.1 `ClusterLowerBoundStmt` (:95) | `clusterLowerBound_of_literature` (`Proofs/Sec4/ClusterLowerBound.lean:44`) | `clusterLowerBound_of_remaining_literature` (`Proofs/Sec4/DerivedInputAssembly.lean:64`) | `clusterLowerBound_proved` (`ClusterLowerBound.lean:18`) |
| Lemma 4.2 `LeastSupersolutionHolderStmt` (:116) | `leastSupersolutionHolder_of_literature` (`Proofs/Sec4/LeastSupersolutionHolder.lean:44`) | `leastSupersolutionHolder_of_remaining_literature` (`DerivedInputAssembly.lean:69`) | `leastSupersolutionHolder_proved` (`LeastSupersolutionHolder.lean:19`) |
| Lemma 4.3 `ClusterSubharmonicBallStmt` (:132) | `clusterSubharmonicBall_of_literature` (`Proofs/Sec4/ClusterGreenIdentity.lean:287`) | `clusterSubharmonicBall_of_remaining_literature` (`DerivedInputAssembly.lean:74`) | `clusterSubharmonicBall_proved` (`ClusterGreenIdentity.lean:261`) |

The derived route is the one committed in 98fedb3 (`Proofs/Sec4/DerivedInputAssembly.lean`, worker z4). It is audited
here independently: the audit applies the literature exports to the providers `wholePlaneGFFAffineInvariance_univ`
(`Proofs/Sec3/DerivedInputAssembly.lean:55`) and `lqgMeasureWeylScaling_univ` (`:62`) and does not use the z4 exports.

## Predecessors exposed by the guards (compile log)

* Literature route. Staged premises: `WholePlaneLQGBallMassBounds`, `WholePlaneGFFAffineInvariance`,
  `LQGMeasureCoordChange`, `LQGMeasureWeylScaling`, `LQGMeasureExistence`, `LQGMeasureNonatomic` (`HarmonicBalls/Proposed/LQG.lean`
  :152, :51, :114, :93, :66, :75). Also `LQGMeasureExistence._proof_1`, the proof obligation Lean abstracts out of that
  Prop's body; it is not a hypothesis. Constant closures: 3423, 3434 and 3645 HarmonicBalls declarations.
* Proof route. No staged predecessor. Closures: 2906, 2917 and 3161 declarations. The proof routes do not reach
  `lqgVolumeGrowthAllScalesStmt_of_literature`, so I2 is their only input.
* Derived route. The providers reach the Props `WholePlaneGFFAffineInvariance`, `LQGMeasureWeylScaling` (as types of the
  providers), `LQGMeasureExistence._proof_1`, and 1214 HarmonicBalls declarations. No Section 4 declaration is reached.
* Every reached Proposed or External constant is a definition (a Prop) or a proof obligation of one; no reached theorem
  or axiom-like constant (guard `sec4CheckStaged`).

### Input I2 traced through its Section 2 producer

I2 (`LQGVolumeGrowthAllScalesStmt`, `Draft/Section2.lean:122`) is a derived input and is not input-free:

* `lqgVolumeGrowthAllScalesStmt_of_literature` (`Proofs/Sec2/Assembly.lean:120`) is
  `lqgVolumeGrowthAllScalesStmt_of_DG hDG hAff hCC wholePlaneGFFMixtureStep_holds hW hE hN`.
* `lqgVolumeGrowthAllScalesStmt_of_DG` (`Assembly.lean:85`) passes `rescaledBallMassUniformStep_of_DG hDG hAff hCC hMix`
  (`Proofs/Sec2/RescaledUniform.lean:289`) and `hW hE hN` to `lqgVolumeGrowthAllScalesStmt_of_rescaled` (`Assembly.lean:50`),
  which applies `lqgVolumeGrowthAllScalesStmt_of_scaled` (`Proofs/Sec2/BallMassReduction.lean:402`, section `Assembled`,
  `include hS hW hE hN`).
* `hMix` is `wholePlaneGFFMixtureStep_holds` (`Proofs/Sec2/MixtureGFF.lean:123`), a proved theorem.
* So I2 uses all six staged premises. Its producer's closure reaches 1638 HarmonicBalls declarations, none in Section 3 or
  Section 4 (guard; no circularity).

## Frozen statements, binder order and drift

* `git diff bd58fe6 HEAD` over `Draft/Section2.lean`, `Draft/Section3.lean` and `Draft/Section4.lean` is empty: the three
  Section 4 statements are unchanged since the freeze commit.
* Binder order of the Stmts: `γ α₀`, then `0 < γ`, `γ < 2`, `α₀ < lqgQ γ`; then `Ω`, `[MeasurableSpace Ω]`, `P`, `hC`,
  `hcirc`, `μ`, `IsWholePlaneGFF P hC hcirc`, `IsLQGMeasureOfField P γ α₀ hcirc μ`; then `∀ᵐ ω ∂P`. In Lemma 4.2 the exponent
  `∃ α` (depending on `γ, α₀` only) comes before the probability space, as [C8] requires.
* Each staged premise quantifies over `Ω`, `[MeasurableSpace Ω]`, `P`, `γ` (and `α₀` where its Prop has it), `hC`, `hcirc`,
  in the order of its Prop, and each export passes it without permutation: the typed applications compile at the frozen order.
* `HarmonicBalls/Proposed/LQG.lean` changed since the freeze only in docstrings (`git diff bd58fe6 HEAD`); the six premise
  definitions are unchanged.

## Kernel orientation, diagonal and integrability

* `greenFunction O x y` (`Defs/Green.lean:70`) is `G_O(x,y)` with the pole in the first argument. It is the junk value `0` on
  the diagonal and off `O` (docstring of `greenFunction`; the paper's `+∞` on the diagonal is not represented).
* `greenPotential O μ x = ∫ y, greenFunction O x y ∂μ` (`Defs/Green.lean:89`). Typed checks in the audit: this equals
  `∫ y, greenFunction O z y ∂μ` at `x = z` by `rfl`, and `greenFunction O x x = 0`.
* The consumers use the same orientation. `subharmonicBallTestClass` (Draft/Section4.lean) uses `greenPotential O ν₁`,
  `greenPotential O ν₂` and `Integrable (greenFunction O z) ν₂` with `ν₂ {z} = 0`, so the diagonal junk does not enter at the
  centre. `GreenFunctionBallStmt` (`Draft/Section2.lean:68`) uses `greenFunction (ball 0 R) x` against `Measure.dirac x`.
  `ClusterGreenPotentialIdentityStep` (`Steps/Sec4/ClusterSubharmonicBall.lean:98`) uses `greenPotential O ν x` and
  `GreenFunctionIntegrableAwayFromPoleStep` (`:110`) uses `Integrable (greenFunction O z) ν`.
* Null-set quantifiers (`∀ᵐ ω ∂P`) and the `∀ z ∈ ball 0 1` scopes are as printed in the frozen Stmts. The Bochner-integrability
  side conditions (`IntegrableOn (greenPotential O ν) Λ μ`, `HasSubMeanValueProperty`) are in the Steps and are not changed.

## Source assumptions (pending operator source-check)

Sources recorded in the docstrings of `HarmonicBalls/Proposed/LQG.lean` (not certified here):
* `WholePlaneLQGBallMassBounds`: Ding-Gwynne 2020, Lemma 3.8.
* `WholePlaneGFFAffineInvariance`: arXiv:1910.04713v2, Section 3.2.2, p. 16.
* `LQGMeasureCoordChange`: Fact 2.1 IV; Duplantier-Sheffield, Proposition 2.1; Sheffield-Wang, Theorems 1.1 and 1.4.
* `LQGMeasureWeylScaling`: Fact 2.1 III.
* `LQGMeasureExistence`: paper Section 2.2, p. 9; Duplantier-Sheffield, Proposition 1.1; Berestycki-Powell, Theorems 2.1 and 3.2
  (the docstring says transfer to the whole-plane singular field is required).
* `LQGMeasureNonatomic`: Fact 2.1 I, p. 9.

Observation for the operator (a source question, not a Lean one): `Proposed/LQG.lean` line 26 says that some of these are
consequences of the definitions, and the paper calls Fact 2.1 I-III "immediate from the definition" (paper line 418). They
are staged as literature premises all the same. The operator decides whether they stay staged.

## Credit (Leonardo Bonanno)

* The derived route makes the audit module a consumer of the LatticeProb library: 303 `LatticeProb` modules are in its import
  closure, through the providers. The closure contains 520 HarmonicBalls files, 59 of which credit him (Section 3 derived
  assembly, Section 6 annulus iteration, Section 8 Birkhoff and circle-density ports, Section 9 affine invariance assembly,
  Section 6 Weyl scaling, `Proposed/Birkhoff.lean`).
* The module header carries the credit line. No other file was edited. The literature-only route has no LatticeProb
  module in its closure (`Audit/Section3InputChecks.lean` guard), so its credit requirement is unchanged.

## Notes for the operator (no blocker)

1. Stale comment. The module doc of `Steps/Sec4/Section4.lean` says that `GreenPotentialBallHolder.lean` cannot be
   imported because `HarmonicBalls.continuousOn_greenFunction_ball` is declared in both `Steps/SecA/Basic.lean` and
   `Proofs/Potential/GreenBall.lean`. The closure of this audit imports `Steps/Sec4/GreenPotentialBallHolder.lean` (through
   `Proofs/Sec4/LeastSupersolutionHolder.lean`) with no name clash. The proved leaf `greenPotentialBallHolderStep`
   (`Steps/Sec4/GreenPotentialBallHolder.lean:15`) is the one that `leastSupersolutionHolder_proved` uses, so the aggregator's
   hypothesis `hHol` is discharged by it on the proof route.
2. GRAPH gaps G3, G4 and G5 have Lean leaves on the proof route, and the closure has only standard axioms: G3 is
   `obstacleConservationOfMassStep3_holds` (`Proofs/Sec3/ConservationOfMassStep3.lean:307`); G4 is
   `greenPotentialBallHolderStep` (above); G5 is `clusterGreenPotentialIdentityStep_of` (`Proofs/Sec4/ClusterGreenIdentity.lean:35`)
   with `greenHarmonicCorrectionBalayageStep_holds` (`Proofs/Sec4/GreenBalayage.lean:186`).
3. No missing predecessor was found, and the written argument of the three routes is not insufficient at the points checked.
   The numbered results stay conditional on the six staged premises (equivalently on I2 for the proof routes). No closure is
   claimed.

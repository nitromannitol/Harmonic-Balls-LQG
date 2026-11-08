# Section 4 derived-input assembly: three exports at the frozen statements

Module: `HarmonicBalls/Proofs/Sec4/DerivedInputAssembly.lean` (new). Worker z4, task `section4-discharge-derived-affine-weyl-inputs`.

## Result

Three exports at the exact frozen statements (`HarmonicBalls/Draft/Section4.lean`; `docs/campaign/FROZEN.md`):

| export (`DerivedInputAssembly.lean` line) | frozen statement | source |
|---|---|---|
| `clusterLowerBound_of_remaining_literature` (:64) | `ClusterLowerBoundStmt` (Draft :95) | Proposition 4.1, prop:lower-bound [C3] |
| `leastSupersolutionHolder_of_remaining_literature` (:69) | `LeastSupersolutionHolderStmt` (Draft :116) | Lemma 4.2, odometer:cont [C8] |
| `clusterSubharmonicBall_of_remaining_literature` (:74) | `ClusterSubharmonicBallStmt` (Draft :132) | Lemma 4.3, lemma:harmonic-ball [C3] |

Each export is the existing `_of_literature` export (`Proofs/Sec4/ClusterLowerBound.lean:44`,
`Proofs/Sec4/LeastSupersolutionHolder.lean:44`, `Proofs/Sec4/ClusterGreenIdentity.lean:287`) applied to the two
universal providers. Each takes exactly four hypotheses: `hDG`, `hCC`, `hE`, `hN` (the retained Props below).

## Derived premises (no hypothesis)

- `hAff` (`WholePlaneGFFAffineInvariance`) is `wholePlaneGFFAffineInvariance_univ` (`Proofs/Sec3/DerivedInputAssembly.lean`),
  the carrier-universal form of `wholePlaneGFFAffineInvariance_proved` (`Proofs/Sec9/AffineInvarianceAssembly.lean:21`).
  Its binders are the carrier, measure and field data only.
- `hW` (`LQGMeasureWeylScaling`, at `α₀ = 0`) is `lqgMeasureWeylScaling_univ` (`Proofs/Sec3/DerivedInputAssembly.lean`),
  the carrier-universal form of `HarmonicBalls.Section6.lqgMeasureWeylScaling` (`Proofs/Sec6/LQGWeylScaling.lean:124`).
  Its binders are the carrier, measure and field data only.
- Input I2 (`LQGVolumeGrowthAllScalesStmt`) is produced inside `lqgVolumeGrowthAllScalesStmt_of_literature`; it is not a
  hypothesis of any export here (guard below).

## Retained explicit hypotheses (four staged Props; not proved, not certified)

- `hDG` `WholePlaneLQGBallMassBounds` (`HarmonicBalls/Proposed/LQG.lean:152`): Ding-Gwynne 2020, Lemma 3.8.
- `hCC` `LQGMeasureCoordChange` (`Proposed/LQG.lean:114`): Fact 2.1 IV of Bou-Rabee-Gwynne.
- `hE` `LQGMeasureExistence` (`Proposed/LQG.lean:66`): Section 2.2 of Bou-Rabee-Gwynne, p. 9.
- `hN` `LQGMeasureNonatomic` (`Proposed/LQG.lean:75`): Fact 2.1 I.

They remain pending operator source-check. This module does not certify them.

## Checks

- `lc HarmonicBalls/Proofs/Sec4/DerivedInputAssembly.lean`: CHECK OK, log `logs/lc/012435-1780798.log` (0 warnings, 0 errors,
  with `-DwarningAsError=true`).
- `lb HarmonicBalls.Proofs.Sec4.DerivedInputAssembly`: BUILD OK, log `logs/lb/012443-1780992.log`.
- Printed axioms (`#print axioms`, in the log): the two universal providers and the three exports depend only on
  `propext`, `Classical.choice`, `Quot.sound`.
- Printed binders (`#check @...`, in the log): each export has the four retained premises as its only binders, with
  `∀ (Ω : Type u) [MeasurableSpace Ω] ...` shapes identical to the existing exports.
- Typed examples at the exact statements (inside the section, so the four premises are the only hypotheses):
  `example : ClusterLowerBoundStmt.{u} := clusterLowerBound_of_remaining_literature hDG hCC hE hN`, and the two others.
- Guard (`#eval` in the file; an error would fail the check): the exports use only standard constants; their types
  contain the four retained Props and none of `WholePlaneGFFAffineInvariance`, `LQGMeasureWeylScaling`,
  `LQGVolumeGrowthAllScalesStmt`; their values apply both universal providers. The constant closure of the two base
  providers reaches 110 `HarmonicBalls` declarations, 2 Proposed Prop definitions (the types of the providers) and one
  auxiliary proof of a Proposed definition (`LQGMeasureExistence._proof_1`). It reaches no `Sec2.Assembly`, `Sec3`,
  `Sec4` declaration, no Proposed or External theorem, and no `LatticeProb` declaration (the guard's list is empty).
- Code scan of the new file for `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`,
  `maxHeartbeats`: none in code. The only match of `opaque` is in a comment of the guard.
- The `lb` log has 365 warning lines, all from `LatticeProb` library modules replayed by the build
  (for example `LatticeProb/Bonanno/LQGMetric/Prob/BinomialTail.lean`: unused `simp` arguments). None names the new module,
  and `lc` on the new file reports no warning under `-DwarningAsError=true`.

## Import inspection (circularity)

- The new module imports `Proofs/Sec3/DerivedInputAssembly`, `Proofs/Sec4/ClusterLowerBound`,
  `Proofs/Sec4/LeastSupersolutionHolder` and `Proofs/Sec4/ClusterGreenIdentity`.
- No module imports `HarmonicBalls.Proofs.Sec4.DerivedInputAssembly` (grep over `HarmonicBalls/` and `Main.lean`).
- The import closure of the new module contains 303 `LatticeProb` modules, through `Proofs/Sec9/AffineInvarianceAssembly`
  (the same count as the Section 3 module).

## Attribution

- Leonardo Bonanno is credited in the module docstring. The `LatticeProb` dependency that brings his library into the
  import closure is named in `Proofs/Sec9/AffineInvarianceAssembly.lean:9-10` and `Proofs/Sec6/LQGWeylScaling.lean:6-7`
  (commit 80b487e).

## Not claimed

- No numbered closure of Proposition 4.1 or Lemmas 4.2 and 4.3. Each export proves its frozen statement from the four
  retained Props. Whether the numbered results are closed is for the operator, after source-check of those Props.
- No edit to `Draft/`, `Defs/`, `Proposed/`, `External/`, `FROZEN.md`, or to any existing assembly.
- Ownership: `tasks/c1.md` claims `HarmonicBalls/Proofs/Sec4/*` by wildcard; the new file is named in `tasks/z4.md`.

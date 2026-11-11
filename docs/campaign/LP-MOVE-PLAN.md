# LP move plan: `HarmonicBalls/LPStage` into the pinned Lattice-Probability tree

Status at HB `HEAD` 1e37db5f (2026-11-11). The 66 modules were moved into the LP repository by five batches of commits on
branch `idla/phase2` (section 1). This file records what was done and what remains. The one-step plan that stood here before
(never run) is superseded by the batches.

Pin: `lakefile.lean` and `lake-manifest.json` still pin LP at `3912597` (`inputRev`). The switch to `52e2f5f` is not done (section 7, step 1).

## 1. Target paths and batches

66 modules are in LP at `52e2f5f` (pushed; an ancestor of `origin/idla/phase2`). The batch of a file is the LP commit that first
added it. Each LP file is the HB mirror with its imports rewritten (section 3).

- **Batch 1, a6b767d (13)**: `Gauss/` CameronMartinDerived, CameronMartinDerived2, CircleAverageApprox, CircleAverageApprox2, GFF,
  GFFAffineInvariance; `Prob/` BirkhoffErgodic, KolmogorovExtension, LocalObservation, PhaseTorus; `Analysis/` PlanarGreen;
  `Topology/` PlaneDomainConvexCompact, PlaneTopology.
- **Batch 2, 79351f7 (36, `LQG/`)**: LQGMassInner, LQGMeasure, LQGMeasureDerived, LQGMeasureFullSupport, LQGMeasureFullSupport2,
  LQGMeasureFullSupport3, LQGMeasureInputs, LQGMeasureLocality, LQGMeasureLocality2, LQGMeasureNonatomic, LQGMeasureNonatomicAll,
  LQGMeasureNonatomicOrigin, LQGMeasureNonatomicMassAffine, LQGMeasureNonatomicMassLocality, LQGMeasureNonatomicMassMixture,
  LQGMeasureNonatomicMassPoly, LQGMeasureNonatomicMassRescaled, LQGMeasureNonatomicMassScaled, LQGMeasureNonatomicMassTail,
  LQGMeasureNonatomicMassWeight, LQGMeasureNonatomicMassWholePlane, LQGMeasureSquare, LQGMeasureSquarePositive, LQGMetric,
  LQGMetricMeasurable, LQGMetricMeasurable2, LQGMetricUniv, LQGWeylScaling, LengthMetric, LengthMetricDerived, LiouvilleGraph,
  MassFunctional, WeylCompositionOuter, WeylCompositionOuter2, WeylInternalClosed, WeylOffOrigin.
- **Batch 3, 3338fbe (2, `Gauss/`)**: GFFCovSymm, GFFExistence.
- **f6c0d7e (2, `Prob/`; not a numbered batch)**: WeylMassMeasurable, WeylSupMeasurable. Both belong to the first plan's 54 files,
  added in their own commit.
- **Batch 4, 9453dd0 (7, `Gauss/`)**: GFFCovPSD1 to GFFCovPSD7.
- **Batch 5, 7b38ebb (6, `LQG/`)**: LocalMeasureKernel to LocalMeasureKernel5, WeylShiftedMass.

Count: 13 + 36 + 2 + 2 + 7 + 6 = 66. The first plan had 54 files; batch 4 (7) and batch 5 (5 new) add 12. `All.lean` is not moved
(section 6, e).

## 2. Status

- LP at `52e2f5f`: 66 of 66 modules present, identical to the HB mirrors after the import rewrite
  (mirror identity table, fleet scratch area, column `identical_52e2f5f`).
- LP tip of `idla/phase2`: 65 of 66 identical. The one difference is `LQG/LocalMeasureKernel5`: the statement is renamed,
  `LocalLQGDecoderCommonFrozenLP` to `LocalLQGDecoderCommon` and `localLQGDecoderCommonFrozen_lp` to `localLQGDecoderCommon`,
  with deprecated aliases for the old names. Its commit is the one titled "LQG: rename the common local decoder statement" in
  `git log --oneline origin/idla/phase2..idla/phase2`. HB consumers switch at the pin bump.
- LP aggregator `LatticeProb/LQG.lean` at `52e2f5f` imports 36 of the 42 `LQG/` modules. The six missing are LocalMeasureKernel,
  LocalMeasureKernel2 to LocalMeasureKernel5 and WeylShiftedMass (batch 5 added no aggregator lines). The default library
  glob covers them; the LP library build at the rename commit passed (10506 jobs).
- HB at `1e37db5f`: the pin is still `3912597`. 32 HB files outside `HarmonicBalls/LPStage/` still import
  `HarmonicBalls.LPStage` modules. `HarmonicBalls/LPStage/` holds all 67 `.lean` files (66 mirrors and `All.lean`); none is archived yet.

## 3. Import rewrites

- Rule: `import HarmonicBalls.LPStage.X` becomes `import LatticeProb.<Dir>.X`, with `<Dir>` from section 1; file names are unchanged.
  Applied in the LP copies: 130 rewritten import lines in total (mirror identity table, column `import_rewrites`).
- HB side (pin switch step): 32 HB files outside LPStage, 40 import lines, from a dry run of the rewrite script (fleet scratch area).
- The LPStage mirrors keep their own LPStage imports until retirement. The archive copies are not built.
- The root `LatticeProb.lean` and the lakefile need no change. The LP aggregator needs six lines (section 2).

## 4. Name-clash probe (before the moves, at `3912597`)

- Textual probe over qualified declaration names (namespace stack tracked): LP 14,467 declarations, LPStage 955,
  0 clashes between them, 0 duplicates inside LPStage.
- The probe does not see `instance`, `notation`, generated names, constructors or projections. The decisive check is the LP
  library build (section 2).

## 5. Other LP files

- `LatticeProb/PORT-PROVENANCE.json` at `3912597`: no mention of `HarmonicBalls` or `LPStage`; no entry is proposed for the moved files.
- `LatticeProbAudit/` is not affected by the move.
- The LP README "Repository layout" has no `LQG/` line at `52e2f5f` (decision c).

## 6. Decisions

a. `LQGMeasureInputs.lean` (LP forms of three Proposed inputs, defined Props, not proved): taken. Moved in batch 2. Its Proposed
   status stays pending the source check.
b. `LocalMeasureKernel` and `LocalMeasureKernel2`: taken. Moved in batch 5, together with LocalMeasureKernel3 to LocalMeasureKernel5.
c. LP README `LQG/` line: open.
d. Pin bump (`lakefile.lean` require rev, `lake-manifest.json`): open. The maintainer makes these edits.
e. `All.lean`: taken. Archived unchanged with the other mirrors in the retirement step (section 7, step 2). Not yet moved.

## 7. Next steps

1. Pin switch: set the LP rev to `52e2f5f` in `lakefile.lean` and `lake-manifest.json`; then the HB import rewrite of the 32 modules
   (dry run, check, apply, build of the 32 modules, one commit).
2. Retire `HarmonicBalls/LPStage/` (67 files) to `archive/` with `git mv`, in one commit, after step 1 and after the last IDLA importer
   is gone: `MatedCRT/FirstPass/LPBridge/LQGMeasureLocalityLP.lean:1` in the IDLA repository still imports `HarmonicBalls.LPStage`.
3. LP repository: add the six missing aggregator lines to `LatticeProb/LQG.lean`.
4. LP README: add the `LQG/` line under "Repository layout" (decision c), if taken.

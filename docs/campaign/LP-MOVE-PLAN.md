# LP move plan: `HarmonicBalls/LPStage` into the pinned Lattice-Probability tree

Planning only (z7, task fp-lpstage-umbrella-refresh-2-and-lp-move-plan, decision R61). No edit in the LP repository, no LP git action.
Probes are read-only; scripts are in `local/` of the worker scratch area (not committed); outputs in `/home/nitro/paper-fleets/hb/scratch-z7/`.

Pinned LP: `.lake/packages/lattice-probability`, commit `3912597` (= `inputRev` of `lake-manifest.json`), 1,485 `.lean` files
(under `LatticeProb/`, `LatticeProbAudit/`, plus `LatticeProb.lean`), root `LatticeProb.lean` with 817 imports.
Lakefile: `lean_lib LatticeProb` globs `andSubmodules LatticeProb`; `lean_lib LatticeProbV435` globs `LatticeProb.LQG`, `.MatedCRT`, `.Bonanno`.
HB side: `HarmonicBalls/LPStage/All.lean` (54 imports, `lb HarmonicBalls.LPStage.All` BUILD OK).

## 1. Target paths (file name = module name; 54 files moved, `All.lean` retired)

- `LatticeProb/Gauss/` (8): GFF, GFFAffineInvariance, GFFCovSymm, GFFExistence, CameronMartinDerived, CameronMartinDerived2,
  CircleAverageApprox, CircleAverageApprox2
- `LatticeProb/Prob/` (6): BirkhoffErgodic, KolmogorovExtension, LocalObservation, PhaseTorus, WeylMassMeasurable, WeylSupMeasurable
- `LatticeProb/Analysis/` (1): PlanarGreen
- `LatticeProb/Topology/` (2): PlaneDomainConvexCompact, PlaneTopology
- `LatticeProb/LQG/` (37, new directory; the aggregator `LatticeProb/LQG.lean` exists, 3 lines, no imports): LQGMassInner, LQGMeasure,
  LQGMeasureDerived, LQGMeasureFullSupport, LQGMeasureFullSupport2, LQGMeasureFullSupport3, LQGMeasureInputs, LQGMeasureLocality,
  LQGMeasureLocality2, LQGMeasureNonatomic, LQGMeasureNonatomicAll, LQGMeasureNonatomicOrigin, LQGMeasureNonatomicMassAffine,
  LQGMeasureNonatomicMassLocality, LQGMeasureNonatomicMassMixture, LQGMeasureNonatomicMassPoly, LQGMeasureNonatomicMassRescaled,
  LQGMeasureNonatomicMassScaled, LQGMeasureNonatomicMassTail, LQGMeasureNonatomicMassWeight, LQGMeasureNonatomicMassWholePlane,
  LQGMeasureSquare, LQGMeasureSquarePositive, LQGMetric, LQGMetricMeasurable, LQGMetricMeasurable2, LQGMetricUniv, LQGWeylScaling,
  LengthMetric, LengthMetricDerived, LiouvilleGraph, MassFunctional, WeylCompositionOuter, WeylCompositionOuter2,
  WeylInternalClosed, WeylOffOrigin, WeylShiftedMass
- Not moved: `All.lean` (its role passes to the LP aggregator); `LocalMeasureKernel{,2}` (z4, committed b01b9b8c; lead decides).
- Topic directories follow the LP README "Repository layout" (`Gauss/` Gaussian measures, `Prob/`, `Topology/`, `Analysis/`) and the
  `LQG` line of the `LatticeProbV435` lib.
- Namespaces are NOT changed by the move (one mechanical step; renames are a later, separate step). Example: MassFunctional keeps
  `LatticeProb.Gauss.Section6`; LQGMeasureLocality keeps `LatticeProb.Gauss`.

## 2. Import rewrites

- Rule: `import HarmonicBalls.LPStage.X` becomes `import LatticeProb.<Dir>.X`, with `<Dir>` from section 1 (file names unchanged).
- Inside LPStage (checked): 0 import lines of any HB module outside `HarmonicBalls.LPStage`; 116 LPStage-internal import lines
  (outside `All.lean`, which has 54). Other imports are already LP or Mathlib: BirkhoffErgodic imports `LatticeProb.Prob.Birkhoff`,
  GFFExistence imports `LatticeProb.Prob.ChentsovPiModification`.
- HB side (after the pin bump, lead): 29 HB files outside LPStage import LPStage modules; they need the same rule.
- LP registration: `LatticeProb/LQG.lean` gains 37 `import LatticeProb.LQG.X` lines (aggregator role). The root `LatticeProb.lean`
  needs no change (it imports 817 of the 1,485 files; the lib globs cover the rest). The lakefile needs no change.

## 3. Name-clash probe (read-only, 2026-11-11)

- Method: awk over the LP files; qualified names of `theorem|lemma|def|abbrev|structure|class|inductive|opaque`, with the
  `namespace`/`section`/`end` stack tracked; `private` declarations skipped (mangled, cannot clash).
- LP: 14,467 declarations. LPStage (57 tracked files, all of `HarmonicBalls/LPStage`): 955 declarations.
- Clashes LPStage vs LP (qualified names): 0. Duplicates inside LPStage: 0. Duplicates inside the 54-module umbrella: 0
  (also confirmed by `lb HarmonicBalls.LPStage.All`, BUILD OK).
- Target paths: none of the 17 probed `Gauss/`, `Prob/`, `Analysis/`, `Topology/` target files exists in LP; `LatticeProb/LQG/`
  is absent, so none of the 37 LQG targets exists.
- Limits: the probe is textual. It does not see `instance`, `notation`, `@[to_additive]`-generated names, or projections and
  constructors. Decisive check: `lake build` of the LP library on the new branch (section 6, step 4).

## 4. Other LP files

- `LatticeProb/PORT-PROVENANCE.json`: 0 mentions of `HarmonicBalls` or `LPStage`; no entry is proposed for the moved files.
- `LatticeProbAudit/`: not affected by the move (its files are not LPStage modules).

## 5. Decisions for the lead (not taken here)

a. `LQGMeasureInputs.lean` defines the LP forms of the three Proposed inputs (`WholePlaneLQGBallMassBoundsLP`,
   `LQGMeasureCoordChangeLP`, `LQGMeasureExistenceLP`; defined Props, not proved). Moving it puts them in the LP library
   with their Proposed status (operator source-check pending). Keep it in HB or move it?
b. `LocalMeasureKernel{,2}` (z4): move in this step or later?
c. Whether the LP README "Repository layout" should get an `LQG/` line in the same branch.
d. The HB pin bump (`lakefile.lean` require rev, `lake-manifest.json`) is the lead's; workers never edit those files.

## 6. One-step LP branch move (for the operator or lead; not run)

1. In the LP repository, create a new branch from `3912597` (never LP main).
2. Copy (do not move in HB) the 54 files of section 1 from `HarmonicBalls/LPStage/` to their LP paths, and apply the rule of section 2.
3. Add the 37 aggregator imports to `LatticeProb/LQG.lean`.
4. `lake build LatticeProb` (default lib) and `lake build LatticeProbV435`; both must pass, with no sorry, admit, axiom or native_decide.
5. One commit on the branch. Push only by the operator.
6. HB side: pin bump (decision 5d), rewrite the 29 importing files, then rebuild the HB modules that import LP (replaces `lb HarmonicBalls.LPStage.All`).

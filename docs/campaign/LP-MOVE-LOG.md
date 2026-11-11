# LP move log

Record of moving HarmonicBalls LPStage modules into the Lattice-Probability (LP) tree, following
`docs/campaign/LP-MOVE-PLAN.md`. The HB files stay in place as the mirror; HB imports are not rewritten
(the pin bump waits for the owner of the public LP repository).

## Batch 1: Gauss, Prob, Analysis, Topology (13 modules)

- LP repository: `/home/nitro/lean/LP-idla-phase2`, branch `idla/phase2` (not pushed).
- LP commit: `a6b767d` (13 new files, 5,273 insertions; no other LP file touched).
- HB commit of the comment cleanup (9 mirror files): see the line "HB commit" below.

### Modules and LP paths

| HB mirror (`HarmonicBalls/LPStage/`) | LP path | LP path rule |
|---|---|---|
| `GFF.lean` | `LatticeProb/Gauss/GFF.lean` | Gauss |
| `GFFAffineInvariance.lean` | `LatticeProb/Gauss/GFFAffineInvariance.lean` | Gauss |
| `CameronMartinDerived.lean` | `LatticeProb/Gauss/CameronMartinDerived.lean` | Gauss |
| `CameronMartinDerived2.lean` | `LatticeProb/Gauss/CameronMartinDerived2.lean` | Gauss |
| `CircleAverageApprox.lean` | `LatticeProb/Gauss/CircleAverageApprox.lean` | Gauss |
| `CircleAverageApprox2.lean` | `LatticeProb/Gauss/CircleAverageApprox2.lean` | Gauss |
| `BirkhoffErgodic.lean` | `LatticeProb/Prob/BirkhoffErgodic.lean` | Prob |
| `KolmogorovExtension.lean` | `LatticeProb/Prob/KolmogorovExtension.lean` | Prob |
| `LocalObservation.lean` | `LatticeProb/Prob/LocalObservation.lean` | Prob |
| `PhaseTorus.lean` | `LatticeProb/Prob/PhaseTorus.lean` | Prob |
| `PlanarGreen.lean` | `LatticeProb/Analysis/PlanarGreen.lean` | Analysis |
| `PlaneDomainConvexCompact.lean` | `LatticeProb/Topology/PlaneDomainConvexCompact.lean` | Topology |
| `PlaneTopology.lean` | `LatticeProb/Topology/PlaneTopology.lean` | Topology |

Namespaces are unchanged. Each LP file is the HB mirror file with only its import lines rewritten.

### Import rewrite

- Rule: `import HarmonicBalls.LPStage.X` becomes `import LatticeProb.Gauss.X`. Every batch-1 module that is
  imported by another batch-1 module lives in `Gauss/`, so one substitution covers the batch.
- Other imports are already LP or Mathlib (`BirkhoffErgodic` imports `LatticeProb.Prob.Birkhoff`).
- Import closure: every LPStage import of a batch-1 file is itself a batch-1 module. No module was dropped.

### Step-3 check (re-check recipe, script-free)

Run from the repository root of each tree, for each batch-1 module `M` in directory `D`:

    diff <(sed -E 's/^import HarmonicBalls\.LPStage\./import LatticeProb.Gauss./' HarmonicBalls/LPStage/M.lean) LatticeProb/D/M.lean

Expected output: empty for all 13 modules. Also `grep -c '^import HarmonicBalls' LatticeProb/*/M.lean` is 0.

Result at the copy (2026-11-11): empty for all 13 modules; 0 leftover `import HarmonicBalls` lines in the LP copies.

### Clash probe (before the copy)

- Method: awk over the LP tree on disk (`LatticeProb/**/*.lean`, 1,490 files, 14,694 declarations) with the
  namespace/section stack, skipping `private`; the batch-1 mirror files give 295 qualified declarations.
- Clashes between batch-1 declarations and LP declarations: 0. Duplicates inside batch 1: 0.
- Target paths already present in LP: none.
- Target paths named in the `mcrt` or `hb` task files: none.
- The probe is textual: it does not see `instance`, `notation`, or generated names. The decisive check is the
  library build below.

### Build

- `lake build` of the 13 modules in the LP tree, under the shared `mcrt/lp.lock`:
  `Build completed successfully (8945 jobs)`; no `sorry`, `admit`, `axiom`, or `native_decide` in the batch files;
  no warnings in the build log.
- The whole LP library was not built (other uncommitted repairs are in that tree).

### Dropped modules

None in batch 1.

### Comment cleanup in the HB mirror (step 2)

Edited (comments only): `GFF`, `PhaseTorus`, `KolmogorovExtension`, `PlaneDomainConvexCompact`,
`CircleAverageApprox`, `CircleAverageApprox2`, `CameronMartinDerived`, `CameronMartinDerived2`, `GFFAffineInvariance`.
No hits: `BirkhoffErgodic`, `LocalObservation`, `PlanarGreen`, `PlaneTopology`.

Removed: task identifiers, worker and owner names, phase and item labels, "LP stage" labels, copy-budget and
`notes/` references, the operator's source-check wording (kept as `PENDING (source check)`), the "First pass:"
label, and mechanical part numbers. The import comment of `CameronMartinDerived2` now reads "Imports:
`CameronMartinDerived` only."

Kept: paper citations, `Proposed` and `Frozen` names and status words, mathematical content, and provenance
pointers to HB source files (`HarmonicBalls/FirstPass/...`, `HarmonicBalls/Steps/...`, `HarmonicBalls/Proofs/...`).
The provenance pointers are kept because the fate of the first-pass tree is an open operator decision (PHASE2-CLEAN-PLAN
section 1, D7) and renames are operator-only.

### Checks on the HB side

- `lc` (per-file compile check) passed for all 9 edited files.
- Comment-only check (`scratch-lk/commentonly.py`, run from the HB root against HEAD before the commit): OK for all
  9 files, so the code of each file is unchanged.
- Umbrella build `lb HarmonicBalls.LPStage.All` was NOT run to completion: it was queued on the shared `hb/lake.lock`
  behind other builds for more than 45 minutes, and was stopped on operator instruction (lead, 13:25 UTC). The LP
  build of the same 13 modules (above) compiled the same text, so the umbrella check is replaced by the comment-only check.

## Batch 2: LQG modules (36)

- LP repository: `/home/nitro/lean/LP-idla-phase2`, branch `idla/phase2` (not pushed).
- LP commit: `79351f7` (36 new files in `LatticeProb/LQG/`, 10,384 insertions; `LatticeProb/LQG.lean` gains 36 import lines; no other LP file touched).
- HB commit of the comment cleanup (36 mirror files): `e84472dd`.

### Modules and LP paths

All 36 go to `LatticeProb/LQG/<Name>.lean` with the HB file name unchanged: LQGMassInner, LQGMeasure, LQGMeasureDerived, LQGMeasureFullSupport, LQGMeasureFullSupport2, LQGMeasureFullSupport3, LQGMeasureInputs, LQGMeasureLocality, LQGMeasureLocality2, LQGMeasureNonatomic, LQGMeasureNonatomicAll, LQGMeasureNonatomicOrigin, LQGMeasureNonatomicMassAffine, LQGMeasureNonatomicMassLocality, LQGMeasureNonatomicMassMixture, LQGMeasureNonatomicMassPoly, LQGMeasureNonatomicMassRescaled, LQGMeasureNonatomicMassScaled, LQGMeasureNonatomicMassTail, LQGMeasureNonatomicMassWeight, LQGMeasureNonatomicMassWholePlane, LQGMeasureSquare, LQGMeasureSquarePositive, LQGMetric, LQGMetricMeasurable, LQGMetricMeasurable2, LQGMetricUniv, LQGWeylScaling, LengthMetric, LengthMetricDerived, LiouvilleGraph, MassFunctional, WeylCompositionOuter, WeylCompositionOuter2, WeylInternalClosed, WeylOffOrigin. Namespaces and declaration names are unchanged.

### Import rewrite

- `import HarmonicBalls.LPStage.X` becomes `import LatticeProb.<Dir>.X`: `LQG` for the 36 modules above; `Gauss`, `Prob`, `Analysis`, `Topology` for the batch-1 modules, as in batch 1.
- Other imports are Mathlib or LP (no batch-2 file imports an HB module outside `HarmonicBalls.LPStage`).
- Import closure: every LPStage import of a batch-2 file is a batch-1 or batch-2 module. Not moved, and not needed by the closure: `GFFCovSymm`, `GFFExistence`, `WeylMassMeasurable`, `WeylSupMeasurable`. Not moved: `WeylShiftedMass`, `LocalMeasureKernel*`, `All.lean`.

### Gates at the time of the move

- (1) Ownership and uncommitted changes: no batch-2 file is named in the OWNS sections of the active HB tasks (z3, z4, z6, z7, n1) or of the active mcrt tasks; no batch-2 mirror file had uncommitted changes (the untracked `LocalMeasureKernel4.lean` and `LocalMeasureKernel5.lean` are outside the batch). Dropped: none.
- (2) `docs/campaign/LP-STAGE-INDEX.md` has no move column yet (no "hold" or "not movable" mark; last commit `9b50f301`). Its intended criteria were applied directly: all 36 modules import only `LatticeProb.*` or `HarmonicBalls.LPStage.*`, and all 36 are imported by `HarmonicBalls/LPStage/All.lean`.
- (3) Clash probe against the LP tree before the commit (1,510 `.lean` files, 14,852 declarations, textual, namespace-aware, `private` skipped): 484 batch-2 declarations, 0 duplicates inside the batch, 0 clashes; none of the 36 target paths existed.
- (4) No mcrt task names `LatticeProb/LQG.lean` or `LatticeProb/LQG/` in its OWNS.

### Mirror check

- Recipe: `diff <(sed -E 's/^import HarmonicBalls\.LPStage\.(\w+)[ \t]*$/…/' HarmonicBalls/LPStage/M.lean) LatticeProb/LQG/M.lean`, with the module-specific directory substituted. Result: empty for all 36 modules; `grep -c '^import HarmonicBalls' LatticeProb/LQG/*.lean` is 0.
- Every `import LatticeProb.*` line of the 36 files resolves to an existing file of the LP tree.

### Comment cleanup in the HB mirror (36 files, commit `e84472dd`)

Removed: stage labels ("LP stage", "(LP stage, ...)"), worker and task identifiers, row, decision, item and part labels, references to generated notes and to external reports, copy-budget remarks, the "First pass:" label, and the "staged for" phrasing (now "included", "taken from" or "stated as"). The operator source-check wording is kept as `PENDING (source check)`. Pointers to HB modules that moved are now LP module paths (`LatticeProb/LQG/<Name>.lean`, `LatticeProb/Gauss/<Name>.lean`).

Kept: paper citations, `Proposed` and `Frozen` names and status words, mathematical content, and provenance pointers to HB source files (`HarmonicBalls/FirstPass/...`, `HarmonicBalls/Steps/...`, `HarmonicBalls/Proofs/...`).

### Checks

- `commentonly.py` against HEAD, before the HB commit: OK for 36 of 36 files (the code of each file is unchanged).
- `lc` per changed file: `CHECK OK` for 36 of 36 files.
- LP build, under the shared `mcrt/lp.lock`: `lake build LatticeProb.LQG` (the aggregator; builds the 36 modules and their closure): `Build completed successfully (8974 jobs)`; no errors, no warnings in the log. The batch files contain no `sorry`, `admit`, `native_decide`, `set_option maxHeartbeats` and no `axiom` declaration.
- Not run: `lake build LatticeProb` and `lake build LatticeProbV435` (whole libraries; the LP tree carries other uncommitted work); `lb HarmonicBalls.LPStage.All` (HB imports are unchanged; the HB side is checked per file with `lc`).

## Batch 3: GFF covariance and existence (2 modules)

- LP repository: `/home/nitro/lean/LP-idla-phase2`, branch `idla/phase2` (not pushed).
- LP commit: `3338fbe` (`LatticeProb/Gauss/GFFCovSymm.lean`, `LatticeProb/Gauss/GFFExistence.lean`; 1,189 insertions; no other LP file touched; the root `LatticeProb.lean` and the LQG aggregator are unchanged).
- HB commit of the comment cleanup (2 mirror files): `7f42025f`.

### Modules and LP paths

- `GFFCovSymm` goes to `LatticeProb/Gauss/GFFCovSymm.lean`; it imports `LatticeProb.Gauss.GFFExistence`.
- `GFFExistence` goes to `LatticeProb/Gauss/GFFExistence.lean`; it imports `LatticeProb.Gauss.GFF`, `LatticeProb.Prob.KolmogorovExtension` (rewritten from the HB mirror import) and `LatticeProb.Prob.ChentsovPiModification` (unchanged).
- Dropped: none.

### Gates

- (1) No active task (hb z3 z4 z6 z7 n1; mcrt) names either file in its OWNS section; the z6 task reads `WholePlaneCovPSDStmt` in place and does not edit these files. No other worker has an uncommitted change in either file.
- (2) `docs/campaign/LP-STAGE-INDEX.md` rows 21-22 read READY both before the LP commit and at the re-check.
- (3) Clash probe: 79 batch-3 declarations, 0 inside the batch, 0 against the LP tree at `f6c0d7e` (14,857 declarations in 1,512 files), run before the LP copies existed and again before the LP commit.
- (4) No mcrt task names `LatticeProb/Gauss/GFFCovSymm.lean` or `GFFExistence.lean`.

### Mirror, hygiene and fidelity checks

- The LP copies differ from the HB mirrors only in the rewritten import lines (`diff` checked); no hygiene hit (no `HarmonicBalls`, `FirstPass`, notes path, owner or task label) in the LP copies.
- HB comment cleanup: `commentonly.py` OK against HEAD for both files; `lc` CHECK OK for both. The declarations and their types are unchanged.
- No `sorry`, `admit`, `axiom`, `native_decide` or heartbeat option in either file.

### Build

- `lake build LatticeProb.Gauss.GFFCovSymm LatticeProb.Gauss.GFFExistence` under the shared `mcrt/lp.lock`: `Build completed successfully (8942 jobs)`; no errors. The 12 warning lines in the log are deprecations in replayed Prob modules (`Chentsov`, `ChentsovPi`, `KolmogorovPi`, `ChentsovPiModification`); none is in the two new files.

### Judgment calls for the lead

- Aggregator: the task asked for import lines in `LatticeProb.lean` or a Gauss aggregator, "in the same style as batch 1". Batch 1 added none (there is no Gauss aggregator, and the `LatticeProb` lib glob covers the directory), so no aggregator line was added. Lead to confirm.
- Held-row wording: the operator note of 13:50 UTC says "GFFExistence and GFFCovSymm stay held (row 29)". The 14:05 task assigns the move and the gate is READY, so the move went ahead on the 14:05 task. Lead to confirm.
- Fidelity: `WholePlaneCovPSDStmt` (the B2 Prop, `GFFExistence.lean`) is defined in that file, not in `HarmonicBalls/External` or `HarmonicBalls/Proposed`; its docstring says only a sketch exists. It is the named hypothesis of `exists_isWholePlaneGFF` and `exists_isWholePlaneGFF_of_psd`. The move carries it unchanged, as the task asks. It needs an operator source-check before any consumer is unconditional.
- Docstring correction (comments only): the B1 bullet said Kolmogorov extension was absent from `LatticeProb`; it is now stated as proved below (`kolmogorovExtensionStmt_proved`).

## Status lines

- HB commit (comment cleanup, 9 mirror files): `70f3786b`, "LPStage batch 1: comment-only cleanup of workflow metacommentary".
  The other 4 mirror files (`BirkhoffErgodic`, `LocalObservation`, `PlanarGreen`, `PlaneTopology`) had no hits and no HB commit.
- Umbrella build `lb HarmonicBalls.LPStage.All`: not run (see above); replaced by the comment-only check.
- LP commit: `a6b767d` on `idla/phase2` (unpushed).
- Step-3 recipe re-run before the HB commit: empty for all 13 modules.
- Batch 2 (36 LQG modules): LP commit `79351f7`; HB comment cleanup `e84472dd`; `lake build LatticeProb.LQG` OK.
- Batch 3 (GFFCovSymm, GFFExistence): LP commit `3338fbe`; HB comment cleanup `7f42025f`; `lake build LatticeProb.Gauss.GFFCovSymm LatticeProb.Gauss.GFFExistence` OK.

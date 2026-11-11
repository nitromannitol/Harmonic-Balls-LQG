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

## Status lines

- HB commit (comment cleanup, 9 mirror files): `70f3786b`, "LPStage batch 1: comment-only cleanup of workflow metacommentary".
  The other 4 mirror files (`BirkhoffErgodic`, `LocalObservation`, `PlanarGreen`, `PlaneTopology`) had no hits and no HB commit.
- Umbrella build `lb HarmonicBalls.LPStage.All`: not run (see above); replaced by the comment-only check.
- LP commit: `a6b767d` on `idla/phase2` (unpushed).
- Step-3 recipe re-run before the HB commit: empty for all 13 modules.

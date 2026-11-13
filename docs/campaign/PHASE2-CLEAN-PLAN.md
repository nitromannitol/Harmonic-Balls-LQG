# Phase 2 item C: hygiene audit and carving plan

Read-only audit (task fp-phase2-clean-plan, worker z6, 2026-11-10), at HEAD 2019e520. No Lean edits, no builds. Target style: [PHASE2-LP-CONVENTIONS.md](PHASE2-LP-CONVENTIONS.md) §7 (subdiffusive-process README). Counts come from `git ls-files`, grep, and a small comment parser (nested `/- -/`, `/-- -/`, `/-! -/`, `--`). They are first-order: re-run them before each edit task. Operator decisions are marked D1 to D10 (section 6).

## 0. Gates already clean (keep green)
- 0 `sorry`, 0 `native_decide`, 0 `TODO`/`FIXME`/`XXX`, 0 `axiom` declarations (12 files match `^axiom` only at the start of a docstring line).
- `set_option maxHeartbeats`: 7 files, all `400000`.
- `admit`: 20 files, all English prose (first 6 checked); no tactic use seen.
- Build scope: `lakefile.lean` has `@[default_target] lean_lib «HarmonicBalls» globs := #[.andSubmodules]`. Every module under `HarmonicBalls/` is built, orphans included. Removing an import does not remove a module from `lake build`.

## 1. Dev artifacts in the tracked tree (3,231 files)
| Item | Count and location | Verdict |
|---|---|---|
| `#print axioms` lines | 3,247 lines in 1,062 files: Proofs 745, FirstPass 180, Steps 102, Audit 30, Assembly 4, Draft 1 | compile-time output inside the library; move to one gate module outside the default build (D6). The Draft file is frozen (D2) |
| other `#check`/`#eval`/`#guard`/`#reduce`/`#synth` | 29 lines; `#check`/`#eval` in 13 files, 7 of them in Audit/ | remove with the gate |
| `HarmonicBalls/Audit/` | 30 files, 3,303 lines (165 `#check`, 93 `example`, 50 theorem, 19 def); 27 have no importer, 3 are imported only by unreached modules | move out of the default build (D9) |
| zero-declaration modules | 4: `Basic.lean` (root header, keep); `Audit/FirstPass11.lean`, `Audit/Section6FullInputChecks.lean`; `FirstPass/S11ah.lean` (import-only aggregator, 37 lines) | per file, in C6 or C7 |
| reach from root | 1,997 of 2,895 HB modules unreached. Root `HarmonicBalls.lean` imports `Basic` and 16 `Proofs/Sec11/Closure` modules; transitive reach 898; 413 modules have no importer; 1,584 are imported only by unreached modules | reach is not an artifact list; recompute after B (D7) |
| `HarmonicBalls/FirstPass/` | 609 files, 0 reached from root, about 78k lines; holds the counted first-pass proofs (`ClosureAll.lean`, `Closure/`, `Frozen/`, `S11*/`); about 575 files carry a comment hit | fate is D7 |
| untracked, not ignored | `scratch/`, `scratch-z4/`, `HarmonicBalls/FirstPass/S2S3S4S9SA/Probe.lean`, `paper/lqg_harmonic_ball-corrected.{aux,bbl,blg,log,out,pdf}`. `.gitignore` has only `.lake/` and `*.olean` | add ignore rules (C1); never delete (not ours) |
| tracked paper products | `paper/Figures/texput.log`, `paper/Figures/harnack-proof-outline.tikz.aux`, `paper/Figures/harnack-type-connected-crossing-oldd.pdf`; `paper/lqg_harmonic_ball.bbl` | untrack or move (D5) |
| unreferenced figures | 35 of 55 tracked figure files (basename grep over `paper/*.tex`, `*.tikz`): both-balls/ 10, both-balls-trun/ 10, harmonic-balls/ 4, harmonic-balls-no-trunc/ 3, comp/ 4, plus 4 single files | check by hand, then move (D5) |
| `% CORRECTION` markers | 33 in `paper/lqg_harmonic_ball-corrected.tex`; 0 in the arXiv source | keep for the errata; decide on a release copy (D5) |
| names in code | `Frozen` in 229 files, `FirstPass` in 520, `Proposed` in 188, `Closure` in 123, `Canonical` in 126 | renames cascade through imports; last, operator only (D10) |

## 2. Metacommentary in HarmonicBalls/ comments
Scope: 2,895 `.lean` files and 15,542 comments: (i) 11,439 declaration docstrings `/-- -/`; (ii) 3,216 file headers (`/-! -/`, and any comment before the first declaration); (iii) 887 plain `--` and `/- -/` after the first declaration. 652 files carry at least one hit of the patterns below.

Each line: occurrences i/ii/iii, files, five samples (file:line, relative to `HarmonicBalls/`).
- **ChatGPT** 233/244/3, 211 files: `Audit/FirstPass11.lean:17`, `FirstPass/Closure/Bridge12.lean:7`, `FirstPass/Closure/Bridge12Canonical.lean:6`, `FirstPass/Closure/Faithful12.lean:14`, `FirstPass/Frozen/S11aj.lean:19`
- **chat N** 81/53/0, 61 files: `Audit/FirstPass11.lean:19`, `FirstPass/Canonical/NotMetricBall.lean:11`, `FirstPass/Canonical/Novelty.lean:9`, `FirstPass/Canonical/Stmts.lean:9`, `FirstPass/Closure/Bridge12.lean:8`
- **Codex** 9/11/2, 10 files: `FirstPass/Frozen/S11rMetric.lean:14`, `FirstPass/S11i/Final11_13.lean:145`, `FirstPass/S11i/Final11_13Close.lean:7`, `FirstPass/S11i/Step8Calibration.lean:18`, `FirstPass/S11i/Step8CalibrationCanonical.lean:6`
- **worker as author** (worker/author/owner/by/from + z,q,n,h digit) 6/425/2, 403 files: `Audit/FirstPass11.lean:7`, `Audit/Section5StagedChecks.lean:7`, `Audit/Section6AnnulusChecks.lean:10`, `Audit/Section9ThreeInputChecks.lean:7`, `FirstPass/Canonical/NotMetricBall.lean:5`
- **operator** (any) 143/226/1, 214 files: `Assembly/ExistenceUniquenessFromEstimates.lean:13`, `Assembly/Section1FromStagedMassInputs.lean:8`, `Audit/FirstPass11.lean:17`, `Audit/Sec11CirclePalmImportChecks.lean:15`, `Audit/Section3InputChecks.lean:16`. Overcount: most hits are mathematical ("pullback operator", "operator norm"). Strict form (operator note/fix/decision/audit, or "operator 2026-"): 162 occurrences in 90 files, e.g. `Defs/Geometry.lean:37`, `Draft/Section1.lean:118`, `Draft/Section10.lean:74`
- **lead** 1/1/0, 1 file: `FirstPass/S11ac.lean:9`, `FirstPass/S11ac.lean:43`
- **fp-task id** 97/195/2, 200 files: `FirstPass/Canonical/NotMetricBall.lean:5`, `FirstPass/Canonical/Novelty.lean:6`, `FirstPass/Canonical/Stmts.lean:6`, `FirstPass/Closure.lean:12`, `FirstPass/Closure/Bridge12.lean:5`
- **FIRST PASS** (capitals) 35/8/0, 14 files: `FirstPass/Canonical/Novelty.lean:47`, `FirstPass/Closure/Main12Canonical.lean:29`, `FirstPass/Frozen/S11c.lean:98`, `FirstPass/Main.lean:10`, `FirstPass/S1S10.lean:16`
- **first pass** (prose) 13/136/0, 133 files: `Audit/FirstPass11.lean:6`, `FirstPass/Closure.lean:14`, `FirstPass/Closure/Bridge12Connected.lean:10`, `FirstPass/Closure/NoWeylMain.lean:6`, `FirstPass/Closure/Sec11.lean:19`
- **PRO re-run tag** 17/17/0, 24 files: `FirstPass/Closure/Bridge12Canonical.lean:6`, `FirstPass/Closure/Faithful12.lean:14`, `FirstPass/Frozen/S11aj.lean:19`, `FirstPass/Frozen/S11c.lean:374`, `FirstPass/Frozen/S11d.lean:81`
- **notes/ paths** (incl. `notes/fp-gaps`) 95/217/2, 220 files: `FirstPass/Closure/Bridge12.lean:7`, `FirstPass/Closure/Bridge12Canonical.lean:6`, `FirstPass/Closure/Faithful12.lean:14`, `FirstPass/Frozen/S11aj.lean:23`, `FirstPass/Frozen/S11c.lean:63`
- **dates 2026-11-** 43/37/0, 48 files: `Audit/FirstPass11.lean:21`, `Defs/Geometry.lean:37`, `Draft/Section1.lean:119`, `Draft/Section10.lean:74`, `Draft/Section11.lean:24`
- **worker token, any context** 155/723/8, 491 files: overcounts (hypothesis names such as `h1`, `n2`); use only the "worker as author" line.
- Zero hits in comments: Claude, Haiku, Opus, GPT, LLM/AI.

Cleaning rule for every edit task:
- Delete: task ids, worker names and chat numbers, model names, operator and lead notes with their dates, `notes/` and `CHATGPT-`/`CODEX-` paths, PRO tags, "FIRST PASS" labels, RETIRED/SUPERSEDED history.
- Keep: paper citations (`line N`, `eq:`, `lemma:` labels, per CONVENTIONS.md line 5), hypothesis provenance (Proposed or External name, theorem, page), mathematical content, and mathematical truth status ("Truth check: TRUE"). Truth status moves to docs (D8); it is not dropped.
- Never change the type or body of a frozen Draft statement (FROZEN.md, 96 lines).

## 3. Docs: campaign-internal versus reader-facing
- Reader-facing candidates: `README.md` (rewrite, section 4); `docs/campaign/CORRECTIONS.md` (79 lines; 18 workflow-word hits: chat, operator, notes/, fp-; scrub); `docs/campaign/INVENTORY.tsv` (78 lines, 0 hits; source of the README results table); `docs/campaign/ERRATA-for-Ewain.md` (188 lines, 0 hits; written for a co-author; D1 whether it ships).
- Campaign-internal (private; D1 picks the folder): PLAN, CONVENTIONS, FROZEN (96 lines), FIRST-PASS-INPUTS, GAPS-HB-1106, MATH-OPEN-20261109, GRAPH (1,952 lines), S11-REPLACEMENT (1,296), Sec11Closure, Sec11ClosureScales, SharedHarnackCrossingConstant, E19-route-b, PHASE2-INVENTORY, PHASE2-LP-CATALOG, PHASE2-LP-CONVENTIONS; `audits/` (251 files); `cex/` (2 files).

## 4. README against the section 7 style
Current `README.md` is 10 lines: H1, one paragraph (formalization of every numbered result, arXiv:2208.11795), and Acknowledgements (Bonanno's lean-formalizations through the `lean-v4.35` line of Lattice-Probability). Gaps:
- The citation is a plain paragraph, not the blockquote of §7.
- No content or status paragraph; status is only "in progress" in the H1. The "64/64 counted first-pass" figure from the operator brief needs operator confirmation; truth checks are pending for some inputs.
- No Main results table (Paper | Lean declaration | Content); generate it from INVENTORY.tsv once D10 fixes the names.
- No Verification section. The axiom checks sit in 1,062 files; claim nothing until D6 lands.
- No Size, Building (Lean v4.35.0-rc2, Mathlib v4.35.0-rc2, pins MarkovProcess 666cda0, EllipticRegularityLean 1e29da0, Lattice-Probability 3912597a70, `lake build`), Repository layout, or How this was built.
- No AI disclosure paragraph (§7 text, verbatim). §7 links `formalization.yaml`, which this repo does not have; LP has one. D3.
- No Authors and citation (BibTeX for arXiv:2208.11795) and no License; there is no LICENSE file in the repo (D3).
- The Acknowledgements link names `nitromannitol/Lattice-Probability` and branch `lean-v4.35`. D4: visibility of LP; keep the wording version-free.
- Leaves-out check: the current text has no model, worker, or harness names. Keep it that way.

## 5. Proposed carving (8 edit tasks)
Shared rules: (a) each file has exactly one owner task; (b) the B-files are the 34 HB files importing `LatticeProb` or `MarkovProcess` at HEAD (Proofs/Sec6 12, GFF 11, Sec8 6, Sec10 1, Sec11 1, Brownian 1, Defs 1, Proposed 1). They stay out of wave 1 and go to C4 after B; (c) edits are comments and docstrings only, with no import, statement or proof change; (d) before a task starts, check `git status` and the task files for other owners of its scope; (e) after each task, rerun the section 0 greps, `lc` on touched files, and `lb` on touched modules.

| Task | Scope | Owned files | Size | Needs | Wave |
|---|---|---|---|---|---|
| C1 docs and root | `README.md`, `docs/**`, `.gitignore`, `paper/Figures/**` | about 330 | docs and figures | D1, D3, D4, D5 | 1 |
| C2 statement layer | `Draft/`, `Defs/`, `Assembly/`, `Proposed/` minus B-files | 37 | 6.4k lines; about 17 hit files | D2, D6 | 1 |
| C3 Proofs rest | `Proofs/` minus Sec6, Sec11, GFF, Brownian, B-files | about 1,010 | about 137k lines; about 24 hit files | D6 | 1 |
| C5 Sec11 and Steps | `Proofs/Sec11/`, `Steps/` minus one B-file | 685 | 69k lines; about 47 hit files | D6 | 1 |
| C4 B-files | the 34 B-files, plus `Proofs/Sec6/`, `GFF/`, `Brownian/` | about 525 | about 62k lines; about 33 hit files | B reports done | 2 |
| C6 FirstPass | `FirstPass/**`; sub-batches a) `S11i,S11c,S11r,S11m` (263 files), b) other `S11*` (about 200), c) top-level, `Closure`, `Frozen`, `Canonical`, `S8c`, `S8d`, `S1S10`, `S5`, `S2S3S4S9SA` (about 150) | 609 | about 78k lines; about 575 hit files | D7, D8, B; then a) b) c) can run in parallel | 3 |
| C7 Audit | `HarmonicBalls/Audit/**` | 30 | 3.3k lines; 165 `#check` | D9, B | 4 |
| C8 renames | module and identifier names (D10) | all | | operator only; one worker; no parallel edits | last |

## 6. Operator decisions
- D1: reader-facing set and folder. Keep `docs/campaign/` private or rename to `docs/internal/`; does ERRATA-for-Ewain ship?
- D2: may docstring-only edits touch frozen Draft statements? Proposal: yes, if a check shows each `…Stmt` type is unchanged.
- D3: license, citation and authors wording; create `formalization.yaml` or drop the §7 link.
- D4: visibility of Lattice-Probability (README link and branch name).
- D5: paper products (untrack `texput.log`, `tikz.aux`, `bbl`, `oldd.pdf`); move the 35 unreferenced figures to `paper/Figures/unused/`; keep or strip `% CORRECTION` markers in a release copy.
- D6: home of the axiom gate (one module outside the default lib, e.g. `checks/`).
- D7: fate of `HarmonicBalls/FirstPass/` (609 files, 0 reached): keep, fold into Proofs, or archive by move. Depends on how B rewires `HarmonicBalls.lean`.
- D8: destination of mathematical status notes in docstrings ("Truth check", "RETIRED", "derived interface"): a status file under docs/, written before C6 strips the workflow context.
- D9: `HarmonicBalls/Audit/` moves out of the default build.
- D10: renames of `Frozen`, `FirstPass`, `Proposed` to `External`, `closure_*`, `firstPass_*`. Operator only, last, one worker; touches every import.

## 7. Open questions
- Two closure chains: `FirstPass/ClosureAll.lean` (orphan) imports `FirstPass/Closure/`; the root imports `Proofs/Sec11/Closure/`. Which one is canonical after B? (operator)
- This audit checked names and comments only; it did not compare the two chains' statements.
- The LP open questions in PHASE2-LP-CONVENTIONS.md §8 are still open.

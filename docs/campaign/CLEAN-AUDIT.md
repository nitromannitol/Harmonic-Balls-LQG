# Clean audit: residual workflow metacommentary

Date: 2026-11-11. Scope: `git ls-files '*.lean'` (3,062 files) and `README.md`, 3,063 files in total, scanned after commit 8cdec65a.
Method: PHASE2-CLEAN-PLAN.md section 2 (cleaning rule), applied line by line with a Python scan (fleet scratch, not committed). Edits are comment-only and were checked with `scratch-lk/commentonly.py`. No `lc` or `lb` was run (K2: one final build later).

## Greps

Applied line by line to each tracked file (a Python equivalent of `grep -n -E`):

    ChatGPT|CHATGPT|Codex|CODEX
    [Cc]hat [0-9]+
    \bfp-|MQ-|\btask [a-z0-9]
    notes/|reports/|docs/campaign|/home/|paper-fleets|scratch-
    FIRST[ -]PASS|first-pass
    \bUTC\b|\b202[56]-1[01]
    \b[Ww]orker\b|\boperator (note|fix|decision|audit)|\blead (lk|lh)|\bOwner\b
    ^\s*#(print|check|eval|reduce|synth)\b

## Table: files and lines still matching, by directory

Lines count matching lines (a line with two patterns counts once). Four uncommitted files of other workers (all in FirstPass) were scanned; none has a hit.

| Directory | Files | Lines | Status |
|---|---|---|---|
| HarmonicBalls/Defs, Assembly, Proposed, Proofs/Sec5 | 0 | 0 | cleaned (0334976f, f5011389, 8cdec65a) |
| all other directories (Steps, Proofs except below, Assembly, archive) | 0 | 0 | clean |
| HarmonicBalls/Proofs/Sec3, Sec4, Sec9 | 3 | 3 | one `#eval` guard block each, kept (decision 1) |
| README.md | 1 | 3 | `docs/campaign` links, kept (decision 2) |
| HarmonicBalls/FirstPass | 6 | 8 | S9c.lean held (1 line); Phase2 5 files, 7 lines (hard skip) |
| HarmonicBalls/Draft | 12 | 45 | frozen (D2), not edited |
| HarmonicBalls/LPStage | 13 | 18 | hard skip |
| HarmonicBalls/Proofs/GFF | 35 | 237 | n4 (C4) |
| HarmonicBalls/Proofs/Sec6 | 1 | 7 | n4 |
| HarmonicBalls/Proofs/Sec11 | 1 | 3 | z7 |
| checks/AxiomGate.lean | 1 | 95 | gate: 92 `#print axioms` kept (D6); line 1 and 3-4 (decision 3) |

Total: 73 files, 419 lines still matching. The `#print axioms` and `#check`/`#eval` lines in Draft, GFF, LPStage, Sec6 and Sec11 belong to frozen or other-owned files and were not touched.

## Commits

- Residual batches (this round): 4df4be3d (39 files), b2e502df (8), 8d19377f (31), 93c408de (2); 8667057f and 4cb7c286 are the audit file.
- C2 batch 1, 0334976f: 14 files of Defs (5), Assembly (3) and Proposed (6), comment-only, all OK.
- C2 batch 2, f5011389: Defs/LBM.lean (fleet path removed), Defs/Green.lean (`docs/campaign` pointer removed), Assembly/ExistenceUniqueness.lean (two `#print axioms` lines removed).
- Residual batch 5, 8cdec65a: README.md (two "first-pass" wording edits), Proofs/Sec3 and Sec4 DerivedInputAssembly (`#check` lines removed), Proofs/Sec5/StagedInputAssembly.lean (three pointers rewritten), Proofs/Sec9/ThreeInputAssembly.lean (one pointer removed).

## Kept items (not workflow metacommentary by rule; lines / files at scan time)

- "staged": 514 / 263, input provenance under Proposed/External.
- "source-check" (pending operator source-check): 74 / 57, input provenance.
- Correction ids `[Cn]`: 174 / 67, correction provenance.
- FROZEN, EXTERNAL and DERIVED status labels: 250 / 58, mathematical input status.
- "candidate" status word: 22 / 14.

## Decisions for the lead

1. Guard blocks (`#eval show CommandElabM Unit from do`, code not comments) in Proofs/Sec3/DerivedInputAssembly.lean (line 102), Proofs/Sec4/DerivedInputAssembly.lean (line 87) and Proofs/Sec9/WeakUniquenessDerivedInputs.lean (line 83) are deliberate in-file checks, not stray commands. Kept. Remove them only if the gate is to be the sole check.
2. `docs/campaign` paths were removed from Lean comments (Defs/Green.lean, Proofs/Sec5/StagedInputAssembly.lean, Proofs/Sec9/ThreeInputAssembly.lean). README keeps its three links to `docs/campaign` (reader-facing; section 3 decision).
3. `checks/AxiomGate.lean` line 1 names a task and a worker, and lines 3-4 point to `docs/campaign`. The file is outside this scope; its owner should clean it (comment-only).
4. `FirstPass/S9c.lean` line 11 (`form [C51] of docs/campaign/CORRECTIONS.md`): held, as in the previous refresh.
5. `FirstPass/S11am.lean:22` "operator gap G1" is not matched by the greps. Kept: it may denote a spectral gap or a campaign id.

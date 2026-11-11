# Clean audit: residual workflow metacommentary

Date: 2026-11-11. Task: fp-clean-residual-audit (worker n3).
Scope: `git ls-files '*.lean'` (3,061 files) and `README.md`, 3,062 files in total.
Method: PHASE2-CLEAN-PLAN.md section 2 (cleaning rule). Edits are comment-only; `scratch-lk/commentonly.py` reported OK on every committed file. No `lc` or `lb` was run (K2: one final build later).

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

## Table: directory, files cleaned, files in flight, residual hits

| Directory | Cleaned (this round) | In flight (owner) | Residual hits |
|---|---|---|---|
| HarmonicBalls/FirstPass (top level, S11*, Closure, Frozen, S8c, S1S10) | 51 | 0 | 0 |
| archive/HarmonicBalls/Audit | 27 | 0 | 0 |
| HarmonicBalls/Proofs/Assembly | 1 | 0 | 0 |
| HarmonicBalls/Proofs/GFF | 0 | 35 (n4, C4) | 0 |
| HarmonicBalls/Proofs/Sec9 | 0 | 2 (n2, C3) | 0 |
| HarmonicBalls/Proofs/Sec5 | 0 | 1 (n2, C3) | 0 |
| HarmonicBalls/Proofs/Sec6 | 0 | 1 (n4, C4) | 0 |
| HarmonicBalls/Proofs/Sec1-4 | 0 | 2 (z3, C3) | 0 |
| HarmonicBalls/Proofs/Sec11 | 0 | 1 (z7) | 0 |
| HarmonicBalls/Defs, Assembly | 0 | 2 (k5, C2) | 0 |
| README.md | 0 | 1 (k5) | 0 |
| checks/AxiomGate.lean | 0 | 1 (D6 gate; `#print axioms` kept) | 0 |
| HarmonicBalls/Draft | 0 | 8 (D2, frozen) | 0 |
| HarmonicBalls/LPStage | 0 | 11 (hard skip) | 0 |
| HarmonicBalls/FirstPass/Phase2 | 0 | 1 (hard skip) | 0 |
| HarmonicBalls/FirstPass/S9c.lean | 0 | 1 (see note 2) | 1 (C51 pointer) |

Other directories (Proofs/Sec8, Sec10, Potential, Sec2, Sec7, Metric, Brownian, Counterexamples, Steps/*, LPBridge, Proposed) have no residual hits.

Totals: 79 files cleaned, 66 in flight, 0 residual in unowned files apart from FirstPass/S9c.lean.

## Commits (this round)

- 4df4be3d residual batch 1 (39 files), b2e502df residual batch 2 (8 files), 8d19377f residual batch 3 (31 files, FIRST-PASS labels), 93c408de residual batch 4 (2 files, chat-number references).
- Earlier C3 wave: 27f25133, 38eabfb1, 22403199 (Proofs/Sec8).

## Kept items (not workflow metacommentary by rule)

- Input status words, "pending operator source-check" and "staged" (163 lines, 74 files): input provenance under Proposed/External.
- Campaign correction ids `[Cn]` (74 lines, 39 files), e.g. "corrected form [C51]". Kept as correction provenance; decision for the lead (see below).
- FROZEN, EXTERNAL and DERIVED status labels (235 lines, 54 files): mathematical input status.
- "candidate" status word (4 lines, 3 files), e.g. Proofs/Sec8/MeanZeroTestEquivalence.lean:5,18.
- Audit titles in archive/HarmonicBalls/Audit (7 lines, 6 files).

## Decisions for the lead

1. `FirstPass/S9c.lean` (1 pointer, line 11, `form [C51] of docs/campaign/CORRECTIONS.md`): held. It is named in the OWNS of `tasks/n3.next.moved-to-n4-20261109.md` (moved to n4). Edit prepared, not committed.
2. "note §6.2-6.4" pointers (14 lines, 9 files in FirstPass/S11ad*): refer to a note that is not in the repository. Kept.
3. `FirstPass/S11am.lean:22` "operator gap G1": kept (ambiguous: spectral gap or campaign gap id).
4. "staged" and "[Cn]" wording: keep or reword (kept here).
5. archive/HarmonicBalls/Audit file titles: keep or rename archive files (not a comment change).

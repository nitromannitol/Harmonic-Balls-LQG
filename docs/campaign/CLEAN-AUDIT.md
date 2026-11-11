# Clean audit: final residual classification

Date: 2026-11-11. HEAD: 89eb098a (tracked files of HarmonicBalls/, checks/ and README.md; 3,039 files). Matching lines: 267 in 89 files. Each line is in exactly one class, by the first rule that applies in the order F, R, H, K, O.
Method: the section 2 greps of PHASE2-CLEAN-PLAN.md, applied to `git show HEAD:<path>` by a Python scan (fleet scratch, not committed). Held: named in the OWNS line of an active task file, or with uncommitted changes. Comment-only audit: no edit, no build.
Update 2026-11-11 at HEAD f75d3b57 (the parent of the commit "Clean comments: last residual items"): the O list is cleared. Items 2, 4, 5, 6 cleaned (4 lines); items 7 and 8 kept (K); items 1 and 3 held for lh (H). Matching lines now 263 in 86 files; the Classes table gives the post-batch counts.

## Greps at HEAD 89eb098a (a line can match several codes)

    A  external-assistant product names                              0
    B  chat-number labels                                            0
    C  campaign id prefixes, the word "task"                        43
    D  notes/, reports/, docs/campaign, home and fleet paths        47
    E  first-pass labels and prose                                   5
    F  UTC and 2026 date stamps                                     13
    G  role words: worker, owner, operator note/fix/decision/audit, lead labels   16
    H  #print, #check, #eval, #reduce, #synth command lines         96
    I  model-family names, LLM, AI                                   1
    J  the word "operator" (overcount; read in K and O)             83

Exact patterns and the scan script: fleet scratch (not committed).

## Classes (267 lines at 89eb098a; 263 after the batch)

| Class | Lines / files | Rule | Examples (file:line) |
|---|---|---|---|
| F frozen | 47 / 12 | Draft/, External/: operator-editable only | Draft/Section1.lean:42, :93; Draft/Section6.lean:54 |
| R retire | 18 / 13 | LPStage/: retires to archive after the pin switch | LPStage/GFFCovPSD1.lean:7, GFFCovPSD3.lean:6, GFFCovPSD4.lean:8 |
| H held | 118 / 8 | OWNS of an active task, or uncommitted; plus the lh-held lines below | checks/AxiomGate.lean:3; FirstPass/Phase2/CanonicalDecoderIdentity.lean:5; FirstPass/Phase2/RootedShiftedNullTransferDerived.lean:13 |
| K kept | 80 / 53 | by decision (below) | Proofs/Sec3/DerivedInputAssembly.lean:102; FirstPass/LPBridge/LQGMeasureFullSupport.lean:19; Defs/StrongMetricSpaces.lean:75 |
| O clean | 0 / 0 | none of the above | none left (see the O section) |

H detail: checks/AxiomGate.lean 92 (90 `#print axioms` lines, lines 3-4 `docs/campaign` pointers); FirstPass/Phase2/RootedShiftedNullTransferDerived.lean 10, RootedShiftedNullTransferSteps.lean 2, RootedShiftedNullTransferEvent.lean 2, RootedDominationJoint.lean 1, CanonicalDecoderIdentity.lean 2 (uncommitted).
lh-held (lead decision 2026-11-11, O items 1 and 3): FirstPass/Phase2/DMSFiniteTiltPosDerived.lean 3 (:7, :13, :381); FirstPass/Phase2/RootedShiftedNullTransferLaw.lean 6 (:13, :15, :46, :96, :183, :222).

K detail:
- guard blocks `#eval show CommandElabM Unit from do`: 4 (Proofs/Sec3/DerivedInputAssembly.lean:102, Proofs/Sec4/DerivedInputAssembly.lean:87, Proofs/Sec9/WeakUniquenessDerivedInputs.lean:83, Proofs/Sec6/ThreeInputAssembly.lean:150; the last added 2026-11-11).
- README.md:57, the AI-assistance disclosure ("The development used AI-assisted proof writing under human direction."): kept, the README must carry it (lead decision 2026-11-11).
- status phrase "pending operator source-check" and variants (input provenance): 30 in 29 files, e.g. FirstPass/LPBridge/LQGMeasureSquare.lean:19.
- mathematical "operator" (operator norm, pullback, Green, transition): 36 in 16 files, e.g. Proofs/Potential/GreenPotentialFunctionalContinuity.lean:17, Proofs/Brownian/PlanarHeatFeller.lean:11.
- citation titles containing "first passage percolation": 5 in 4 files, e.g. Defs/LQGMetric.lean:195, Proposed/LQG.lean:187, FirstPass/Frozen/S11c.lean:62.
- `[C51]` pointer to docs/campaign/CORRECTIONS.md: FirstPass/S9c.lean:11.
- README links to docs/campaign (reader-facing): README.md:22, :24, :52.

## Stale globs (not held)

Task files closed or untouched since 2026-11-06 reserve no file. Their globs: Proofs/Sec3/*, Proofs/Sec4/*, Proofs/Sec6/*, Proofs/Sec11/*, Proposed/MetricProperness.lean, Proofs/Brownian/*.lean. Their hits are classified above by content.

## Still to clean (O): none left

Cleaned in the batch "Clean comments: last residual items" (items 2, 4, 5, 6):
- FirstPass/Phase2/EventSampleRepresentationProof.lean:31: question id and "math desk" note removed; "TRUE as typed" kept.
- FirstPass/Phase2/WeylAeMeasurableDerived.lean:16: operator-route sentence removed.
- FirstPass/S11am.lean:22: gap label G1 removed.
- Proofs/Sec6/ThreeInputAssembly.lean:56: audit pointer and its parenthetical removed; "his" became "the" (no pronoun for the named author).
Moved: item 7 to K; item 8 to K; items 1 and 3 to H (lh).
Open, not on the lead's list: FirstPass/Phase2/WeylAeMeasurableDerived.lean:15 "(l.389-391)" points into an unnamed written argument; kept as a status description.

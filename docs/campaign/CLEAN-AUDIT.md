# Clean audit: final residual classification

Date: 2026-11-11. HEAD: 89eb098a (tracked files of HarmonicBalls/, checks/ and README.md; 3,039 files). Matching lines: 267 in 89 files. Each line is in exactly one class, by the first rule that applies in the order F, R, H, K, O.
Method: the section 2 greps of PHASE2-CLEAN-PLAN.md, applied to `git show HEAD:<path>` by a Python scan (fleet scratch, not committed). Held: named in the OWNS line of an active task file, or with uncommitted changes. Comment-only audit: no edit, no build.

## Greps (a line can match several codes)

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

## Classes (267 lines)

| Class | Lines / files | Rule | Examples (file:line) |
|---|---|---|---|
| F frozen | 47 / 12 | Draft/, External/: operator-editable only | Draft/Section1.lean:42, :93; Draft/Section6.lean:54 |
| R retire | 18 / 13 | LPStage/: retires to archive after the pin switch | LPStage/GFFCovPSD1.lean:7, GFFCovPSD3.lean:6, GFFCovPSD4.lean:8 |
| H held | 109 / 6 | OWNS of an active task, or uncommitted | checks/AxiomGate.lean:3; FirstPass/Phase2/CanonicalDecoderIdentity.lean:5; FirstPass/Phase2/RootedShiftedNullTransferDerived.lean:13 |
| K kept | 78 / 52 | by decision (below) | Proofs/Sec3/DerivedInputAssembly.lean:102; FirstPass/LPBridge/LQGMeasureFullSupport.lean:19; Defs/StrongMetricSpaces.lean:75 |
| O clean | 15 / 7 | none of the above | list below |

H detail: checks/AxiomGate.lean 92 (90 `#print axioms` lines, lines 3-4 `docs/campaign` pointers); FirstPass/Phase2/RootedShiftedNullTransferDerived.lean 10, RootedShiftedNullTransferSteps.lean 2, RootedShiftedNullTransferEvent.lean 2, RootedDominationJoint.lean 1, CanonicalDecoderIdentity.lean 2 (uncommitted).

K detail:
- guard blocks `#eval show CommandElabM Unit from do`: 3 (Proofs/Sec3/DerivedInputAssembly.lean:102, Proofs/Sec4/DerivedInputAssembly.lean:87, Proofs/Sec9/WeakUniquenessDerivedInputs.lean:83).
- status phrase "pending operator source-check" and variants (input provenance): 30 in 29 files, e.g. FirstPass/LPBridge/LQGMeasureSquare.lean:19.
- mathematical "operator" (operator norm, pullback, Green, transition): 36 in 16 files, e.g. Proofs/Potential/GreenPotentialFunctionalContinuity.lean:17, Proofs/Brownian/PlanarHeatFeller.lean:11.
- citation titles containing "first passage percolation": 5 in 4 files, e.g. Defs/LQGMetric.lean:195, Proposed/LQG.lean:187, FirstPass/Frozen/S11c.lean:62.
- `[C51]` pointer to docs/campaign/CORRECTIONS.md: FirstPass/S9c.lean:11.
- README links to docs/campaign (reader-facing): README.md:22, :24, :52.

## Stale globs (not held)

Task files closed or untouched since 2026-11-06 reserve no file. Their globs: Proofs/Sec3/*, Proofs/Sec4/*, Proofs/Sec6/*, Proofs/Sec11/*, Proposed/MetricProperness.lean, Proofs/Brownian/*.lean. Their hits are classified above by content.

## Still to clean (O): every line

1. FirstPass/Phase2/DMSFiniteTiltPosDerived.lean:7, :13, :381: campaign question id; notes/ path at :13.
2. FirstPass/Phase2/EventSampleRepresentationProof.lean:31: campaign question id; "math desk" note.
3. FirstPass/Phase2/RootedShiftedNullTransferLaw.lean:13, :15, :46, :96, :183, :222: campaign question id; notes/ path at :15.
4. FirstPass/Phase2/WeylAeMeasurableDerived.lean:16: status sentence naming the operator's route.
5. FirstPass/S11am.lean:22: campaign gap label G1.
6. Proofs/Sec6/ThreeInputAssembly.lean:56: docs/campaign/audits pointer.
7. Proofs/Sec6/ThreeInputAssembly.lean:150: `#eval` guard block; the kept list covers Sec3, Sec4 and Sec9 only.
8. README.md:57: sentence on the development process; no class covers it.

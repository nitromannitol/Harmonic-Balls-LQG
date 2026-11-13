# Audit round 2 responses (HB errata, tex and docstrings)

Source: `notes/fp-gaps/OPUS-AUDIT-R2.md` (fleet). Task fp-audit-r2-hb-errata-and-responses (z7); refresh fp-audit-r2-refresh-and-binder-trades (z7, 2026-11-11, rows checked against git log and the tree). Status key: FIXED (commit) / IN PROGRESS (worker, task) / AWAITING OPERATOR APPROVAL / DISPUTED (reason) / NOT CONFIRMED (where it went). Commit hashes: `docs/campaign/AUDIT-R2-FIXED.done`.

## Major (A): HB errata

| Item | Status | Where |
|---|---|---|
| M1 printed defects of Lemma 11.12 and Lemmas 11.15–11.17 | FIXED (commit) | ERRATA-for-Ewain.md Part 1, C44 item; ERRATA-INTERNAL.md line 8 corrected (reason was wrong); O2 amendment stays internal |
| M2 [C48] and [C51] falsity claims | FIXED (commit) | Email: "not proved", no counterexample claimed (lead R43); CORRECTIONS.md C48, C51; INTERNAL C48/C51 and C10/C51 conflict, one line each |
| M3 Part 3 gaps | FIXED (commit) | Part 3: selection-rule sentence at the top; 16 bullets, each checked at the printed lines; G17 not confirmed (see below) |
| M4 Theorem 5.5 two-sided continuity | FIXED in the email (commit); tex patch APPLIED as [C71] (clarification; op 13:10) | Email C59 reworded; tex patch at corr:1056 applied as [C71] (missing detail; no new statement) |

## HB(A) minors

| Item | Status | Where |
|---|---|---|
| C61 email formula | FIXED (commit) | Email C61 Problem and Correction use a = a'/1001^{γ\|α₀\|}; CORRECTIONS.md C61 entry |
| C69 stale sites | FIXED (commit) | Tex: corr:1232, 1357, 1633, 1651, 1896, 2093 (alpha_0 written out, marker [C69]). C62 p-check (z7, 2026-11-11): RESOLVED, no edit. ERRATA-for-Ewain.md C62 (lines 226–229) matches the corrected statement of Lemma 6.7 (`lemma:very-good-annuli-hit`, corr:1379–1386: a = a(b,p,γ,α₀,β⁻); C^±_1, C^±_2 depend on a,γ,p,α₀,β⁻; N_1(b,p,γ,α₀,β⁻) in the last line). The earlier "corr:1357 has no p" was a wrong line: corr:1357 is inside the proof of `lemma:good-annuli` (corr:1349–1361), which writes a = a(b,γ,α₀) with the universal p fixed in that proof (a notation point in the proof; tex not owned by z7) |
| C7 wording | FIXED (commit) | Email C7 Problem: the failure comes from the slit (z in ∂O), any pole in O∖Λ works |
| C42 Ω wording | FIXED (commit) | Email C42 no longer blames the printed text for Ω; tex marker corr:3216; CORRECTIONS.md C42 |
| C68 relabel | FIXED (commit) | Email Lemma A.6 marked "(clarification)"; tex marker corr:4521 |
| C37 / C39 overstatement | FIXED (commit) | Email C37 (negative height harmless) and C39 (ergodic route) reworded; CORRECTIONS.md C37 |
| C58 "unbound" | FIXED (commit) | Email C58 uses "unbound T"; tex marker corr:865 already reads "unbound". Maintainers' dispute not supported (agreed) |
| C47 | FIXED (commit) | Moved to ERRATA-INTERNAL.md (corr:47 is in neither the email nor INTERNAL before) |
| C55 / C62 placement | FIXED (commit) | Moved from Part 1 to Part 2 (Section 4 and Section 6) |
| Self-citations corr:3437, 4039, 4089, 4197 | FIXED (commit) | \ref/\eqref to lemma:harmonic-comparison-chain, lemma:odometer-annuli, lemma:odometer-bound-lqg-mass, theorem:harmonic-balls, theorem:full-theorem-minus-uniqueness, eq:ball-volume, lemma:volume-growth. Label for "(2.11)" chosen by context (eq:ball-volume): reviewer to confirm |
| Orphan figure fig:crossing-argument (corr:2646–2652) | FIXED (commit) | Figure commented out with a [C48] marker; original kept commented |
| [C70] residual (measurability of A, corr:3065) | FIXED as disclosure (commit) | Email C70 "Open" line; tex comment before corr:3063; CORRECTIONS.md C70 |
| Early ledger [C17] / [C43] | FIXED (commit) | CORRECTIONS.md "Not adopted" line and INTERNAL [C17] line: [C17] statement part is adopted as [C43] |
| CORRECTIONS-PROPOSED.md absence | FIXED (commit) | Not in the repository; it is the fleet ledger hb/CORRECTIONS-PROPOSED.md (175 lines), with no entry for C27–C36 (INTERNAL, early items) |
| X1 [C44] O2 over-corrected | FIXED (commit) | See M1 |

## HB(B) minors

| Item | Status | Where |
|---|---|---|
| Stale docstring [C15] for [C64] | FIXED (commit) | HarmonicBalls/Draft/Section6.lean:49, 451 (docstring only; lc OK) |
| Stale docstring [C9] for [C58] | FIXED (commit) | HarmonicBalls/Draft/Section5.lean:40, 162, 167 (docstring only; lc OK) |
| Duplicate binders hDec/hLoc, derivable binders hWCont, hMf, hDiam, hDsm, hfull, no manifest | IN PROGRESS (z7, fp-audit-r2-refresh-and-binder-trades): per-binder outcomes in "Line 40 binder outcomes" below. Traded: hMf and hDiam in row 11.16, `firstPass_11_16_corrected_derivedInputs34` (FirstPass/Phase2/DerivedInputs34.lean, z7). Not traded: hDec/hLoc, hWCont, hfull (no counted row binds them), hDsm (no binder-free theorem). No manifest: COUNTED-MANIFEST.md exists (f2473471, z6) | Lean |

## Lean rows (not owned by z7)

| Item | Status | Owner and partial commits |
|---|---|---|
| M9 (B1 decoder) | IN PROGRESS (partial). hK LocalMeasureKernelStmt (FirstPass/S11r/Frozen.lean:140) DERIVED; hLoc/hDec LocalLQGDecoderCommonFrozen (FirstPass/Frozen/S11c.lean:383) DERIVED; hN2 LocalMetricReplacementFrozen (FirstPass/Frozen/S11rMetric.lean:33) PARTIAL, z4 checking (not verified by z7); hA10 (FirstPass/Frozen/S11i.lean:37) REPLACED by the subcritical input hSub, `DMSLemmaA10WholePlaneMarkedSub` (FirstPass/Frozen/S11i.lean:57), in the event file (1e37db5f, `RootedShiftedNullTransferEvent`) and in the canonical null transfer (163e9bb2); hSub is still a binder with its source-check open | z4, fp-phase2-b1-decoder-derive; derived by localMeasureKernelStmt_derived (a9b0d406) and localLQGDecoderCommonFrozen_derived (9deeaee0), ledger da31111f; earlier partial commit 78d91e32 |
| M10 (B2 DMS joint positive radius) | IN PROGRESS. Chain, each with its commit: canonical null transfer `shiftedDecoderNullTransferCanonicalStmt_derived` (RootedShiftedNullTransferDerived.lean:470) 163e9bb2 (takes hSub); decoder identity `canonicalDecoderIdentityStmt_derived` 08492ee1 (z7, binder-free); canonical domination 0c69b39e (z4, RootedDominationCanonical.lean); JointPos cylinders J1–J3 19e4d64a, 87d0d101, b2a40602 (n1); DMSJointPosOfFinite J4–J6 28b5ad0d, bb4a83dc (z3). PENDING: J7 `dMSJointPos_of_sub` (DMSJointPosOfFinite.lean:327, in the working tree, not committed; z3); final `localRootedFieldMeasureDomination_of_sub` (z4, not yet in the tree); row-8 counted trade `DerivedInputs33` (n1, not yet in the tree). Commit c1f49ef0 is partial | z3 (fp-phase2-dms-joint-positive-radius), z4 (canonical domination, final), n1 (cylinders, row 8); z7 (identity) |
| M11, M12 (hholder), HB(B) binders | M11: OPEN, forall-xi forms stay conditional on named Props, canonical-xi consequences in 6883fd97; M12 (hholder): BLOCKED, stays a binder (cited HB Prop 2.5 input; route B is an operator decision), 94723b16; HB(B): PARTIAL, 6 wrappers discharged in 94723b16 (DerivedInputs23), hDsm still bound, manifest f2473471 | z6, fp-audit-r2-binders |

## Line 40 binder outcomes (z7, fp-audit-r2-refresh-and-binder-trades, 2026-11-11)

Method. A counted row binds a Prop by its type, not by its name (binder `hM` of row 11.16 is `LQGMassInnerMeasurableFrozen`). A script scan (scratch-z7/rows_bind.py, not committed) read the binder types of all 65 rows of COUNTED-MANIFEST.md at their declaration (rows 2.1, 2.2, 2.5, 2.6 have none). Ledger rows 8, 17, 23 (docs/campaign/PHASE2-DERIVATION-STATUS.md) are bound by counted rows 3.5, 5.2, 8.2, 9.2, 11.6 (row 8) and 11.10 (rows 17, 23), so no trade touches them. A wrapper is written only where the count drops and the row binds none of 8, 17, 23.

- hDec / hLoc (`LocalLQGDecoderCommonFrozen`, FirstPass/Frozen/S11c.lean:383): no counted row binds it. Theorem `localLQGDecoderCommonFrozen_derived` (FirstPass/Phase2/LocalDecoderCommonDerived.lean:1859) has no binders (9deeaee0). Outcome: already gone for the counted rows. The duplicate hLoc = hDec of the four Theorem 1.2 forms is discharged in DerivedInputs23 (94723b16), which is not a counted row.
- hWCont (`WeylMetricCompositionContinuousOuterFrozen`, FirstPass/Frozen/S11j.lean:111): no counted row binds it. Theorem `weylMetricCompositionContinuousOuter_derived` (FirstPass/Phase2/WeylCompositionOuterDerived.lean:1220) has no binders. Outcome: already gone for the counted rows.
- hMf (`LQGMassInnerMeasurableFrozen`, FirstPass/Frozen/S11k.lean:65): bound by counted row 11.16 (FirstPass/Phase2/DerivedInputs31.lean:24, binder hM). Theorem `lqgMassInnerMeasurable_derived'` (FirstPass/Phase2/CircleAverageLocalityLinkDerived.lean:196) has no binders. Outcome: DERIVED-wrapper, `firstPass_11_16_corrected_derivedInputs34` (FirstPass/Phase2/DerivedInputs34.lean, z7; lc OK).
- hDiam (`LQGInternalDiamInnerMeasurableFrozen`, FirstPass/Frozen/S11k.lean:87): bound by row 11.16 (binder hDiam). Theorem `lqgInternalDiamInnerMeasurable_derived` (FirstPass/Phase2/InnerMeasurableDerived.lean:78) has one binder hFA, the forall-form of `LQGMetricFieldAxioms`, which is the 11.16 binder hAx (`LQGMetricFieldAxiomsUnivFrozen`, FirstPass/Frozen/S11j.lean:149). Outcome: DERIVED-wrapper in DerivedInputs34 (applied to hAx). With hMf, the count of row 11.16 goes from 11 to 9.
- hDsm (`SmallMetricDiameterLargeMassStmt`, the Draft statement of 11.9, HarmonicBalls/Draft/Section11.lean:201): bound by row 11.16 as its binder hD (counted by firstPass_11_9). Theorems: `firstPass_11_9` (FirstPass/S11d.lean:39, 8 explicit binders), `closure_11_9` (FirstPass/Closure/Sec11.lean:269, 16), `closure_11_9_derivedInputs17` (FirstPass/Phase2/DerivedInputs17.lean:325, 11), `closure_11_9_derivedInputs2` (DerivedInputs2.lean:24, 15), `closure_11_9_derivedInputs3` (DerivedInputs3.lean:32, 14). None is binder-free. Outcome: not traded (every theorem has more binders than hD). Non-counted declarations (FirstPass/S11m/Final11_12.lean:79, Clean11_12.lean:81, CertificateAssembly.lean:251) also bind it.
- hfull (`LQGMeasureFullSupportStmt`, HarmonicBalls/Draft/Section2.lean:109): no counted row binds it. Its theorems carry section `include`s, which the counting caveat of the manifest does not show: `lqgMeasureFullSupportStmt_of_existence` (Proofs/Sec9/LQGExistenceConsequences.lean:46, include hDG hCC hE at :26), `lqgMeasureFullSupportStmt_of_stronger_singularity` (Proofs/Sec2/SingularAtomAtZero.lean:67, include at :44), `lqgMeasureFullSupportStmt_of_volumeGrowth` (Steps/Sec2/VolumeGrowth.lean:220, one binder h). No binder-free theorem. Outcome: not traded. DerivedInputs23 discharges it for the 8.2 row with hDG hCC hE.

## Round-1 rows marked Partial or No for HB

| Round-1 row | Status |
|---|---|
| HB X1 [C44] | FIXED (M1) |
| HB A3 [C42] | FIXED (above) |
| HB A5 α₀ dependence | FIXED for the C69 sites (above); p in C62 resolved (line 19) |
| HB A6 gap list | FIXED (M3) |
| HB per-item: C58, C47, C48/C51 | FIXED (above) |
| HB B1 / B2 / B3 hholder (M9, M10, M12) | IN PROGRESS (Lean rows above). B1 (M9): hK and hLoc/hDec DERIVED, hN2 PARTIAL, hA10 now the input hSub (open). B2 (M10): see the M10 chain. B3 (M12 hholder): BLOCKED, stays a binder (row M11, M12 above) |

## Not confirmed in the printed text

- G17 (Lemma 6.6 proof, spacing hypothesis; GRAPH.md:1373): cited lines orig:1373–1383 are LaTeX comments (each starts with %); the compiled proof at orig:1370–1372 refers to Lemma good-annuli. Recorded in ERRATA-INTERNAL.md, not in the email.

## Disputed

None in this round. Note on the audit's wording: CORRECTIONS-PROPOSED.md is not in the repository but exists in the fleet directory, as recorded above.

## AWAITING OPERATOR APPROVAL (new mathematical text)

M4: left-continuity repair for the corrected proof of Theorem 5.5 (replaces the sentence "by Proposition 5.4" at corr:1048–1056). Three lines (MQ-lh-24 FINAL THREE LINES, from GRAPH.md:1335 (G7)) inserted in the tex as [C71] (op 13:10):

1. Left-continuity: if $x\in\Lambda_t\setminus\overline{\bigcup_{s<t}\Lambda_s}$, a ball $B_\varepsilon(x)$ has positive $\mu_h$-mass and misses $\bigcup_{s<t}\Lambda_s$, so $\mu_h(\Lambda_t)>\mu_h\big(\overline{\bigcup_{s<t}\Lambda_s}\big)$.
2. This contradicts $\mu_h(\Lambda_t)=t=\lim_{s\uparrow t}\mu_h(\Lambda_s)$ (Lemma 3.4, Proposition 8.1), once $\mu_h\big(\partial\bigcup_{s<t}\Lambda_s\big)=0$ is established.
3. Hence $\Lambda_t\subset\overline{\bigcup_{s<t}\Lambda_s}$, and with Propositions 5.2 and 7.2 the family $t\mapsto\Lambda_t$ is Hausdorff-continuous on $(0,T)$.

Open points for the operator: (a) line 2 needs the boundary-null property of the union, which GRAPH.md:1335 does not state; (b) the Lean proof at `HarmonicBalls/Proofs/Sec5/LeftContinuity.lean:163` (`regularizedClusterHausdorffContinuity_of_steps`) is conditional on six named Section 5 step hypotheses (ClusterOpenLaplacianStmt, ClusterMonotoneStmt, ClusterConservationOfMassStmt, ClusterBoundaryMeasureZeroStmt, and two more), so it is not a closed proof of this repair.

## Compile results

- `pdflatex` on `paper/lqg_harmonic_ball-corrected.tex` (two passes, output in scratch-z7/tex): 0 errors, 0 undefined references. Undefined citations remain because bibtex was not run.
- lc: HarmonicBalls/Draft/Section5.lean and Section6.lean: CHECK OK (docstring-only diff).

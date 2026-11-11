# Audit R1 responses: Harmonic balls (HB) part

Source: `notes/fp-gaps/OPUS-AUDIT-R1.md` (operator note 01:00, task fp-audit-r1-hb-errata-ledger-responses). Scope: HB findings only. The IDLA findings (A7–A10, B4–B7) concern `idla/MatedCRT` and are **not** this repository's HB part; they are listed at the end for completeness and handled by the IDLA owner.

Status key: **FIXED** (commit, worker) · **IN PROGRESS** (worker, task) · **DISPUTED** (justification) · **OPEN** (owner, what is left) · **NO CHANGE** (audit gives no fix).

Commits: `3518c8f8`, `987564de` (z7, email and ledger); `04195351` (z3, tex markers). Email: `docs/campaign/ERRATA-for-Ewain.md`. Ledger: `docs/campaign/CORRECTIONS.md`. Internal notes: `docs/campaign/ERRATA-INTERNAL.md`.

## Critical and major (part A)

| Finding | Status | Evidence / what is left |
|---|---|---|
| X1 [C44]: O₂ error attributed to printed paper | FIXED (3518c8f8, z7; tex comment 13f73d62, z7) | O₂ sentences removed from the email (3518c8f8). The tex marker at `lqg_harmonic_ball-corrected.tex:3670` is reworded (13f73d62): it says what was printed (bump proof with unbuffered supports and a shrinking factor), that the printed paper contains no Ō₂, and that the containment is an amendment (2026-11-09). No eq:large-mass-low-diam item added (per lead). |
| A1 `\appendix` deleted | FIXED (04195351, z3) | `\appendix` restored; marker `[C65]` at corrected:4187. |
| A2 sentence deleted in [C65] hunk | FIXED (04195351, z3) | Restored, citing Lemma 2.4 of the corrected draft; marker at corrected:4192. CAVEAT (z3): the restored sentence needs the step "polynomially high probability (Lemma 2.4) ⇒ a.s. volume growth for all small r" (Borel–Cantelli over dyadic scales and monotone interpolation), which the printed text also leaves unwritten. Operator to decide. |
| A3 [C42] "Printed" claim false | FIXED (3518c8f8, 04195351) | Email item reduced: the printed buffers exist, and the missing one is B₁₀δ₀(W) ⋐ T plus the component Ω. Tex marker at corrected:3216 now states this (z3). Ledger C42 updated. |
| A4 Lemma 6.4 proof after [C61] | FIXED (04195351, z3; 987564de, z7) | Tex marker at corrected:1247: transfer ratio `a=(C₁/C₂)a'`, and the `|z|^{-α₀γ}` factor replaced by the sup/inf ratio (≤ 1001^{γ\|α₀\|}). Email C61 item and ledger C61 updated. |
| A5 α₀/β⁻ dependence inconsistent | FIXED in tex (04195351, z3; [C69] at corrected:389) | z3 lists the sites it changed: Prop 6.1, Lemma 6.3, Lemma 6.7 (A₁, A₂), Lemma 6.11, Prop 7.2, Lemma 10.1. CAVEAT (z3): the Prop 6.1 and Lemma 10.1 proofs were not re-read for α₀ dependence. I did not re-check corrected:1126, 1350, 1389, 1978, 2094, 2572 line by line; that check is z3's. Email: C55, C61, C62 tagged minor; Part 2 "Standing convention" C69 (987564de). |
| A6 Prop 11.2 gap, and the gap list | FIXED for Prop 11.2 (04195351, z3; email 987564de, z7); other gaps listed, not repaired | Prop 11.2 routed through the boundary-union identity (`[C70]` at corrected:3061); z3: the arrival-time argument is cited, not re-proved. Email Part 3 lists G1, G2, G3, G5, G7, G13, G15, G27/G29, G38 (3518c8f8). z3: none of these G-items is repaired in the tex; the G7 fix is a candidate that changes a claim used elsewhere, not made. Operator to route. |

## Per-item rows, part A (audit l.173–212)

| Item | Status | Note |
|---|---|---|
| C7 Thm 1.1 class | FIXED (3518c8f8) | Slit construction named: O = B_R∖S, S a slit through z, pole y ∈ ∂Λ(z); G_O(z,y)=0 while ∫_Λ G_O(·,y)dμ_h>0. Audit's diagnosis confirmed; the Lean counterexample is `Proofs/Counterexamples/LiteralTestClass.lean` (cited by the audit, not re-checked here). |
| C1 Lemma 2.4 | FIXED (3518c8f8) | "and in both displays" removed; the displays are unchanged. |
| C5 eq. (2.13) locator | FIXED (3518c8f8) | Header now "Equation (2.13)"; ledger C5 header fixed. |
| C3 | NO CHANGE | Audit: Y/Y/Y, no note. |
| C6, C12, C53, C38 | NO CHANGE | Audit: Y/Y/Y, no note. |
| C47 | FIXED (3518c8f8) | Dropped (Notation section removed from the email). |
| C52, C54 | FIXED (3518c8f8) | Moved to Part 2 (minor). |
| C66, C67, C68 | FIXED (3518c8f8) | Moved to Part 2, Appendix A (minor). C68: "not well defined" replaced by the concrete defects (t free, s₁ ≤ 0, s₂ unscoped). |
| C55 | FIXED (3518c8f8) | Tagged minor: dependence bookkeeping. |
| C61 | FIXED (987564de; tex 04195351) | See A4. |
| C62 | FIXED (3518c8f8) | "N₁ displayed in the proof" → "in the statement" (corrected:1376). Tagged minor. |
| C56 | FIXED (3518c8f8; tex 04195351) | Email matches corrected:833. Ledger rewritten to the adopted text (not the all-t alternative). Second marker at corrected:2173 (z3). |
| C57 | FIXED (3518c8f8) | "the radius r is unbound". |
| C58 | NO CHANGE (partly) | The audit's "unbounded → unbound" note was applied to C57 (the free radius). "an unbounded T" is kept; the audit gives no fix for it. |
| C60 | FIXED (3518c8f8) | Added: for z ∉ U the cluster is empty (Λ = ∅). |
| C63, C64 | NO CHANGE | Audit: Y, no note. |
| C59 | FIXED (3518c8f8) | Rephrased: Lemma 5.7 is a fixed-centre equality in law; cites Prop 10.6 (via Prop 10.7 correction). |
| C50 | FIXED (3518c8f8) | Rephrased. The correction already cites Prop 10.6; the printed proof's Lemma 10.1 is quoted as printed. |
| C23 | FIXED (commit that adds this file) | Locator "Equation (6.2), §6.1"; moved to Part 2, Section 6 (minor). Ledger C23 header fixed. |
| C18 | NO CHANGE in email | Stale 2094 is a tex item (A5). |
| C22 | FIXED (3518c8f8; tex comment 13f73d62, z7) | Lebesgue examples named (slit breaks 9.1(2), fat Cantor set breaks 9.3); correction now "the class of the corrected Theorem 1.1 ([C7])". Tex marker at corrected:2408 reworded (13f73d62): it states the printed text and the change, without "enlarged". |
| C48 | FIXED (3518c8f8) with a flag | Cites §3 of steps4-final.tex. **Flag:** that note is in the fleet notes (`hb/notes/wpn-steps4/`), not in this repository. The operator must decide whether to attach it or move the construction into the paper (the same principle as audit A7). |
| C51 | FIXED (3518c8f8) with a flag | Same citation. Conflicts with INTERNAL [C10]; see INTERNAL below. |
| C49 | NO CHANGE | Audit: Y/Y, no note. |
| C37, C39, C40, C41, C45, C46 | NO CHANGE | Audit: Y or P, fix right, no note. C46's Prop 11.2 gap is A6 (FIXED). |
| C43 | FIXED (3518c8f8) | Email aligned to the certificate form: event E^α(M) ⊂ Ĝ, measurable w.r.t. h^α|_{B₇}, P > 0. |
| C42 | FIXED (3518c8f8, 04195351) | See A3. |
| C44 | See X1 | |
| C65 | NO EMAIL CHANGE | Hunk damage is A1 and A2 (FIXED, 04195351). |

## Unmarked damage

| Item | Status | Note |
|---|---|---|
| A1, A2 | FIXED (04195351, z3) | See above. |
| Stale figure `fig:crossing-argument` (corrected:2647–2651) | DISPUTED (evidence: z3, 04195351) | z3: caption and label identical to the printed text at orig:2574–2583; no edit made. The audit's "stale" claim is not supported. |
| Garbled sentence at printed line 1834 | DISPUTED (evidence: z3, 04195351) | z3: the line is identical to the printed orig:1767, parentheses balanced; no edit made. |

## INTERNAL section

| Item | Status | Note |
|---|---|---|
| Stripped from the email | FIXED (3518c8f8) | Moved to `docs/campaign/ERRATA-INTERNAL.md`. |
| [C10] "not shown false" vs [C51] | OPEN (operator) | Contradiction recorded in ERRATA-INTERNAL.md. The email follows [C51]. Operator to reconcile with the 04:35 ruling on Prop 9.2. |
| [C24] "equivalent alternative" | FIXED (3518c8f8) | Now "strictly stronger". |
| [C27]–[C36] | FIXED (3518c8f8) | "no record in this repository; never assigned here (operator asked, R21)". |

## HB Lean (part B)

| Item | Status | Note |
|---|---|---|
| B1 Section 11 bridge inputs | IN PROGRESS (z4, task fp-audit-r1-b1-measurability-inputs; earlier task fp-audit-r1-b1-local-metric-replacement) | Partial commit 95e4ac15 (z4): the unrooted clause (18) of `LocalMetricReplacementStmt` is derived from `unrooted_identity_fixedMetric` in `HarmonicBalls/FirstPass/Phase2/LocalMetricReplacementDerived.lean`; binders hFA (Proposed), hB1, hCM, hPhi (unprinted frozen). z4 report: BLOCKED-partial; the rooted clause and the full bridge are blocked by unprinted steps. |
| B2 `hL1` (Lemma 8.2 step) | IN PROGRESS (z3, task fp-audit-r1-b2-rooted-domination) | No commit yet. Not an email item. |
| B3 I1 `hFull`, I2 `hgrowth` | IN PROGRESS (z6, task fp-audit-r1-b2-b3-lean, step DerivedInputs4) | No commit yet. The repo already derives them (audit). |
| B3 `hholder` (Prop 2.5) | DISPUTED | Lead ruling (operator 04:40 UTC): Prop 2.5 / hholder stays a cited input; the paper proves it by citation to Ponce §16.2. No change. |
| MINOR (B) HB list | IN PROGRESS (z6, fp-audit-r1-b2-b3-lean) | Retired `hWeyl` and duplicate binders; universe-0 corollary of 11.13; ξ via `Classical.choice` (record); Lean Prop 5.2 docstring (all-t form); `greenPotentialClass` reading (record). |

## IDLA findings (not this repository's HB part)

A7, A8, A9, A10, B4, B5, B6, B7 concern `idla/MatedCRT`. They are not HB rows and are not addressed here.

## Open after this round

1. Lead: email and ledger for IDLA are not in this repository. Not mine.
2. Operator: steps4-final.tex attachment or relocation (C48, C51); INTERNAL [C10] vs [C51]; A2 volume-growth step (z3 observation).
3. z3: A5 site check (Prop 6.1 and Lemma 10.1 proofs); G-item repairs routed by operator.
4. z4 (B1, rooted clause and full bridge), z3 (B2 hL1), z6 (B3 I1/I2, MINOR Lean): pending their reports.
5. Round 2 (this file): tex markers C44 (corrected:3670) and C22 (corrected:2408) reworded in 13f73d62; ledger in 1db565b3.

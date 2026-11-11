# HB errata: internal notes (not for the email to the co-author)

Moved out of ERRATA-for-Ewain.md on the audit R1 response (fp-audit-r1-hb-errata-ledger-responses, z7). Patches of the email items are in CORRECTIONS.md. Row-by-row status of the audit findings is in AUDIT-R1-RESPONSES.md.

## Internal items

- [C44] O_2 amendment (author-approved 2026-11-09): the closure of O_2 lies in the closed 4delta-neighbourhood of W, which lies in B_{5delta}(W). This is our own replacement text, not a printed error: the printed paper contains no O_2 (grep of paper/lqg_harmonic_ball.tex is empty). The marker at paper/lqg_harmonic_ball-corrected.tex:3670 said "Printed in the corrected draft"; it was reworded to "Not printed: ... amendment of this draft" (z7, this round). The email therefore cites no O_2 sentence.
- [C44] Lemma 11.17 and its three-event proof: moved out of ERRATA-for-Ewain.md on the operator 05:10 ruling; reason: our own text, not a printed error (operator 05:10).
  - *Printed:* the bump proof of the three events uses unbuffered supports and an incorrect shrinking factor.
  - *Problem:* the supports and the strict inequalities do not suffice.
  - *Correction:* replace the bump proof by local certificates and a joint large-mass, small-diameter construction. The inner separation $(v-\delta)-(u+\delta)>8\delta$ is unchanged.
- [C48], [C51]: the positive-probability existence of such holes is constructed in §3 of steps4-final.tex. That note lives in the fleet notes (hb/notes/wpn-steps4/steps4-final.tex), not in this repository. The email cites it and says it is to be attached; the operator must decide whether to attach it or move the construction into the paper (the same principle as audit A7 for IDLA).
- [C42]: reduced, not dropped. The printed eq:metric-delta0-choice does give buffers (audit A3 checked at the printed lines 3243-3247). The only buffer missing is B_{10delta0}(W) inside T; the connected component Omega is also unspecified.

## Early items [C1]-[C36] (not in the email)

- [C2]: superseded by [C65] (the same Appendix A volume-growth correction; upper exponent beta+).
- [C4]: superseded by [C53] (Lemma 3.4, equality case) and [C67] (Lemma A.5).
- [C8]: superseded by [C55] (Lemma 4.2 exponent depends on gamma and alpha_0).
- [C9]: superseded by [C58] (Proposition 5.4: T = T(z), delete "for all r > 0").
- [C10]: superseded by [C51]; the weak form Lambda subset A is part of [C51]. Operator 04:35: the Stmt of Prop 9.2 stays as printed (PARTIAL), and the weak form is proved separately. CONFLICT, for the operator to reconcile: the earlier note "the printed conclusion is not shown false" contradicts [C51], which states that the printed inclusion fails at the last time a bounded hole disappears. The email follows [C51]. Do not repeat the "not shown false" wording anywhere.
- [C11]: superseded by [C43] (Lemma 11.12 for every alpha < Q with the hat-G event; operator E13).
- [C13]: superseded by [C52] (Lemma 3.3).
- [C14]: superseded by [C54] (Lemma 3.5) and [C68] (Lemma A.6).
- [C15]: superseded by [C64] (Lemma 6.13).
- [C16]: superseded by [C49] (Proposition 10.6: components of C minus the closure).
- [C17]: not adopted (operator 04:35: proof gap only, no statement change).
- [C19]: superseded by [C57] (Proposition 5.3).
- [C20]: superseded by [C58] (Proposition 5.4 containment).
- [C21]: superseded by [C60] (Lemma 5.8: z in U).
- [C24]: superseded by [C63] (finite-supremum premise). The early text "z not in closure(A)" is strictly stronger than the [C63] premise, not an equivalent alternative.
- [C25]: superseded by [C61]. The early text names a(b,gamma); the counterexample (docs/campaign/cex/AlphaUniformity.md section 2) refutes Lemma 6.4, whose constant is a(b,p,gamma). Lemma 6.3 with a(b,gamma) is true (section 6.2 of the same file).
- [C26]: superseded by [C62] (AlphaUniformity.md section 5).
- [C27]-[C36]: no record in this repository; never assigned here (operator asked, R21). No correction text, analysis or adoption exists for these tags in CORRECTIONS-PROPOSED.md (not in this repository), FROZEN.md, ESCALATIONS.md, GAPS-HB-1106.md or docs/campaign/cex/. The adopted early set is C1-C9, C11-C16, C18-C26 (C10 in weak form only).

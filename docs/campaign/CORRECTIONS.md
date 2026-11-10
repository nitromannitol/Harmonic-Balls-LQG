# Corrections in paper/lqg_harmonic_ball-corrected.tex

Surgical corrections to arXiv:2208.11795, each marked `% CORRECTION [Cn]` in the corrected draft, with the published text, the
corrected text and a one-line reason. Section 11 changes below are author-approved 2026-11-06.

- [C37] Lemma 11.8 proof: replace a potentially negative bump and universal drift comparison by a nonnegative bump and the fixed-parameter factor `1201^(-γ|α₀|)`; the former claims are not valid uniformly.
- [C38] `lemma:harmonic-comparison-chain`: point to `eq:alternate-size-2-full` instead of `eq:alternate-size-2`; the potential has variable aspect ratio.
- [C39] `lemma:mu_h-bad-and-harnack`: replace the direct origin application of the separated-annulus bound by rooted ergodicity and rooted-field transfer; separation alone does not prove rooted frequency.
- [C40] `lemma:no-exterior-cone-condition`: use a rational cone contained in the given cone instead of a containing rational cone; sector mass is monotone under inclusion.
- [C41] `lemma:no-exterior-cone-condition`: replace `A_{3r,5r}` by `A_{r,2r}` in the good-event inequality; the event controls the latter annulus.

- [C42] Pinch-event geometry: replace the figure-only separation assumptions with explicit buffers and the connected component `Ω`; the certificate's bump supports and paths require them.
- [C43] `lemma:mu_h-pinch-positive-probability`: replace `α₀ = 0`, `P[tilde G₁(0)] > 0` by the local-certificate assertion for `hat G₁` and every `α < Q`; the tilde names a different event and the rooted application needs `α = γ`.
- [C44] Pinch positive-probability proof: replace the original bump construction by local certificates and the joint large-mass/small-diameter construction; the printed shrinking factor and support/strictness estimates do not suffice. Amended 2026-11-09 (author-approved): the containment of closure(O_2) uses the closed 4delta-neighbourhood of W, inside B_{5delta}(W); the open B_{4delta}(W) version fails on the outer circle.
- [C45] `lemma:mu_h-pinch-bad`: replace the direct frequency transfer from the unrooted field by dilation ergodicity and the rooted-field identity at `α = γ`; global metric comparisons cannot simply be treated as annular-local.
- [C46] `prop:not-metric-balls`: replace the center-zero and informal time-union reasoning with an arbitrary-center obstruction and an arrival-time boundary-union identity; metric balls can have arbitrary centers and the exceptional time set is random.
- [C47] Variable-annulus `SG` hyperlinks: link `SG_{s₁ρ,s₂ρ}` and `SG_{3r,6r}` to `eq:alternate-size-2-full` rather than `eq:alternate-size-2`; the latter has a fixed aspect ratio.

Full audited replacement submissions are retained in `docs/campaign/S11-REPLACEMENT.md`.

Sections 9 and 10 changes below are author-approved 2026-11-09 ("Yes clusters can have holes"). Their text is taken from the
independently audited written proofs in the fleet file notes/wpn-steps4/steps4-final.tex (sha256 f9da848c8ad8179d8fd94795b7bfbdf198d7e8aefd38c72c89788a56acdba932),
Section 3 (audit AUDIT-steps4-t3-r3.md, VERDICT CORRECT) and Section 5 (AUDIT-steps4-t5.md); Lean-specific remarks are omitted.

- [C48] `lemma:crossing-connected` (Lemma 10.5): replace the printed lemma, false because clusters can have holes, by the deterministic statement that finitely many small-scale crossings give local connectedness, no cut points and simple-loop complementary boundaries (Torhorst's theorem, Jolivet-Loridant-Luo arXiv:1411.6776v1 Thm 3.1).
- [C49] `prop:boundary-simple-loop` (Prop 10.6): components of `C \ closure` instead of `B_1 \ closure` (proposal [C16]); proof from Lemma 10.1 and [C48]. The outer component of `B_1 \ closure` has a disconnected frontier.
- [C50] `prop:boundary-simple-loop-full-cluster` (Prop 10.7) proof: pathwise dyadic rescaling of Prop 10.6, a countable intersection and the closure identity of Theorem 5.5, instead of a union bound over uncountably many centres with the fixed-centre Lemma 5.7. Statement unchanged.
- [C51] `prop:sub-harmonic-ball-uniqueness` (Prop 9.2): the weak form `Λ ⊂ A ⊂ Λ̂`, `μ_h(A \ Λ) = μ_h(Λ̂ \ A) = 0`, with `A = Λ̂` when `A` is regular open (proposal [C10]). The printed `Λ̂ ⊂ A` fails at the last time a bounded hole disappears. The paper does not use Prop 9.2.

## [C52] Lemma 3.3 (lemma:monotonicity), lines 648–650 (applied 2026-11-10 with the author's approval)
This is a notation/definedness repair only; it does not change the intended monotonicity assertion. Patch [H1] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C53] Lemma 3.4 (lemma:conservation-of-mass), lines 653–655 (applied 2026-11-10 with the author's approval)
Pure symbol correction: Appendix A uses a general `\mu`, but this numbered result is in the LQG setting and must use `\mu_h`. Patch [H2] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C54] Lemma 3.5 (lemma:cluster-compatibility), lines 661–665 (applied 2026-11-10 with the author's approval)
The event may depend on the fixed outer radius `R`, exactly as in the current wording, but not on `t`. Patch [H3] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C55] Lemma 4.2 (odometer:cont), lines 720–732 (applied 2026-11-10 with the author's approval)
The random constant `C` remains uniform in `t,z,x,y`; only the deterministic exponent’s displayed dependence changes. Patch [H4] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C56] Proposition 5.2 (prop:continuity) and its concluding proof line, lines 827–838 and 2105–2109 (applied 2026-11-10 with the author's approval)
To retain the stronger all-`t` statement, make only the `B_\epsilon(0)` edit and insert the missing boundary-touching extension proof; the current draft does not contain that argument. Patch [H5] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C57] Proposition 5.3 (prop:boundary-measure), lines 839–845 (applied 2026-11-10 with the author's approval)
This binds no new parameter; it matches the actual result proved later in the paper. Patch [H6] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C58] Proposition 5.4 (prop:conditional), lines 857–860 (applied 2026-11-10 with the author's approval)
The same conull event is still simultaneous in all `z`; only `T` is allowed to depend on the sample and the center. Patch [H7] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C59] Theorem 5.5 proof, lines 955–1013 (applied 2026-11-10 with the author's approval)
This is the one non-surgical patch: it replaces the fixed-center law argument by the pathwise covariance already used later in correction [C50], and it makes the all-center event and two-sided continuity explicit. Patch [H8] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C60] Lemma 5.8 (lemma:strong-compatibility) and Proposition 1.3 locality proof, lines 1020–1046 (applied 2026-11-10 with the author's approval)
This keeps Proposition 1.3 for every deterministic open `U`; only the auxiliary domain-cluster lemma is restricted to the regular domains actually used in the exhaustion. Patch [H9] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C61] Lemma 6.4 (lemma:annulus-hit), lines 1189–1194 and 1207–1208 (applied 2026-11-10 with the author's approval)
No dependence on `r` or `z` is introduced; only the fixed insertion parameter must be displayed. Patch [H10] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C62] Lemma 6.7 (lemma:very-good-annuli-hit), lines 1311–1319 (applied 2026-11-10 with the author's approval)
If `\beta^-` is fixed once and for all as a function of `\gamma`, its displayed dependence may be suppressed; the `\boldsymbol{\alpha}_0` dependence may not be presented as uniform. Patch [H11] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C63] Lemma 6.9 (lemma:harmonic-odometer-comparison), lines 1463–1471 and line 1490 (applied 2026-11-10 with the author's approval)
This excludes exactly the false `\infty\cdot0` case; all later applications have a finite comparison supremum. Patch [H12] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C64] Lemma 6.13 (lemma:low-mass-implies-small-odometer), lines 1714–1716 (applied 2026-11-10 with the author's approval)
The paper may retain the single universal `C_3` supplied by Lemma 6.6; Lean’s stronger “every `C_3>0`” version need not be printed. Patch [H13] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C65] Appendix A setup, equation eq:volume-growth, lines 4131–4135 (applied 2026-11-10 with the author's approval)
This is the exponent pair used by the formal statement and by the LQG volume bounds cited earlier. Patch [H14] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C66] Appendix A obstacle and supersolution class, lines 4155–4164 (applied 2026-11-10 with the author's approval)
The off-pole formulation is equivalent to majorization of the `-\infty` obstacle and matches the formal admissible class. Patch [H15] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C67] Appendix A.5 (lemma:appendix-conservation-of-mass), lines 4394–4396 (applied 2026-11-10 with the author's approval)
The proof already uses `\mu` throughout, so no proof edit is needed. Patch [H16] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C68] Appendix A.6 (lemma:appendix-cluster-compatibility), lines 4457–4465 (applied 2026-11-10 with the author's approval)
This is the exact deterministic quantifier order audited in chat 210; the rest of the proof is unchanged. Patch [H17] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

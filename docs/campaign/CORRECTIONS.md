# Corrections in paper/lqg_harmonic_ball-corrected.tex

Surgical corrections to arXiv:2208.11795, each marked `% CORRECTION [Cn]` in the corrected draft, with the published text, the
corrected text and a one-line reason. Section 11 changes below are author-approved 2026-11-06.

- [C37] Lemma 11.8 proof: replace the bump by a nonnegative one (a negative height is harmless; the change simplifies) and the universal drift comparison by the fixed-parameter factor `1201^(-γ|α₀|)`; the weight comparison depends on α₀.
- [C38] `lemma:harmonic-comparison-chain`: point to `eq:alternate-size-2-full` instead of `eq:alternate-size-2`; the potential has variable aspect ratio.
- [C39] `lemma:mu_h-bad-and-harnack`: replace the direct origin application of the separated-annulus bound by rooted ergodicity and rooted-field transfer; separation alone does not prove rooted frequency.
- [C40] `lemma:no-exterior-cone-condition`: use a rational cone contained in the given cone instead of a containing rational cone; sector mass is monotone under inclusion.
- [C41] `lemma:no-exterior-cone-condition`: replace `A_{3r,5r}` by `A_{r,2r}` in the good-event inequality; the event controls the latter annulus.

- [C42] Pinch-event geometry: eq:metric-delta0-choice already prints buffers for `U`, `V`, `W`, `T`, `Q'`, `Q`, but not `B_{10δ₀}(W) ⋐ T`; add that buffer; the connected component `Ω` belongs to the replacement argument and is specified there (audit R2: `Ω` is not an object of the printed paper). The certificate's bump supports and paths require them.
- [C43] `lemma:mu_h-pinch-positive-probability`: replace `α₀ = 0`, `P[tilde G₁(0)] > 0` by the local-certificate assertion for `hat G₁` and every `α < Q`; the tilde names a different event and the rooted application needs `α = γ`.
- [C44] Pinch positive-probability proof: replace the original bump construction by local certificates and the joint large-mass/small-diameter construction; the printed shrinking factor and support/strictness estimates do not suffice. Amended 2026-11-09 (author-approved; INTERNAL, not in the email): the containment of closure(O_2) uses the closed 4delta-neighbourhood of W, inside B_{5delta}(W). The printed paper contains no O_2 (grep), so the open B_{4delta}(W) version is not a printed error; the marker at corrected:3670 said "Printed in the corrected draft"; it was reworded (not printed; amendment) in the round that adds this line.
- [C45] `lemma:mu_h-pinch-bad`: replace the direct frequency transfer from the unrooted field by dilation ergodicity and the rooted-field identity at `α = γ`; global metric comparisons cannot simply be treated as annular-local.
- [C46] `prop:not-metric-balls`: replace the center-zero and informal time-union reasoning with an arbitrary-center obstruction and an arrival-time boundary-union identity; metric balls can have arbitrary centers and the exceptional time set is random.
- [C47] Variable-annulus `SG` hyperlinks: link `SG_{s₁ρ,s₂ρ}` and `SG_{3r,6r}` to `eq:alternate-size-2-full` rather than `eq:alternate-size-2`; the latter has a fixed aspect ratio.

Full audited replacement submissions are retained in `docs/campaign/S11-REPLACEMENT.md`.

Sections 9 and 10 changes below are author-approved 2026-11-09 ("Yes clusters can have holes"). Their text is taken from the
independently audited written proofs in the fleet file notes/wpn-steps4/steps4-final.tex (sha256 f9da848c8ad8179d8fd94795b7bfbdf198d7e8aefd38c72c89788a56acdba932),
Section 3 (audit AUDIT-steps4-t3-r3.md, VERDICT CORRECT) and Section 5 (AUDIT-steps4-t5.md); Lean-specific remarks are omitted.

- [C48] `lemma:crossing-connected` (Lemma 10.5): replace the printed lemma, which we have not proved for clusters with holes (we do not claim it is false), by the deterministic statement that finitely many small-scale crossings give local connectedness, no cut points and simple-loop complementary boundaries (Torhorst's theorem, Jolivet-Loridant-Luo arXiv:1411.6776v1 Thm 3.1).
- [C49] `prop:boundary-simple-loop` (Prop 10.6): components of `C \ closure` instead of `B_1 \ closure` (proposal [C16]); proof from Lemma 10.1 and [C48]. The outer component of `B_1 \ closure` has a disconnected frontier.
- [C50] `prop:boundary-simple-loop-full-cluster` (Prop 10.7) proof: pathwise dyadic rescaling of Prop 10.6, a countable intersection and the closure identity of Theorem 5.5, instead of a union bound over uncountably many centres with the fixed-centre Lemma 5.7. Statement unchanged.
- [C51] `prop:sub-harmonic-ball-uniqueness` (Prop 9.2): the weak form `Λ ⊂ A ⊂ Λ̂`, `μ_h(A \ Λ) = μ_h(Λ̂ \ A) = 0`, with `A = Λ̂` when `A` is regular open (proposal [C10]). The printed `Λ̂ ⊂ A` is not proved (no counterexample is claimed; audit R2 M2, lead R43). The paper does not use Prop 9.2.

## [C52] Lemma 3.3 (lemma:monotonicity), lines 648–650 (applied 2026-11-10 with the author's approval)
This is a notation/definedness repair only; it does not change the intended monotonicity assertion. Patch [H1] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C53] Lemma 3.4 (lemma:conservation-of-mass), lines 653–655 (applied 2026-11-10 with the author's approval)
Pure symbol correction: Appendix A uses a general `\mu`, but this numbered result is in the LQG setting and must use `\mu_h`. Patch [H2] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C54] Lemma 3.5 (lemma:cluster-compatibility), lines 661–665 (applied 2026-11-10 with the author's approval)
The event may depend on the fixed outer radius `R`, exactly as in the current wording, but not on `t`. Patch [H3] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C55] Lemma 4.2 (odometer:cont), lines 720–732 (applied 2026-11-10 with the author's approval)
The random constant `C` remains uniform in `t,z,x,y`; only the deterministic exponent’s displayed dependence changes. Patch [H4] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C56] Proposition 5.2 (prop:continuity) and its concluding proof line, lines 827–838 and 2105–2109 (applied 2026-11-10 with the author's approval)
Adopted: the translated ball `B_\epsilon(z)` is replaced by the ordinary `\epsilon`-neighbourhood, and continuity is stated only for the times before the cluster reaches the boundary of the unit ball, which is the scope the second part of Section 5 proves (markers at corrected:833 and corrected:2173, z3, commit 04195351). Not adopted: the all-`t` alternative (edit only `B_\epsilon(0)` and insert a boundary-touching extension proof), because the draft does not contain that argument. Patch [H5] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C57] Proposition 5.3 (prop:boundary-measure), lines 839–845 (applied 2026-11-10 with the author's approval)
This binds no new parameter; it matches the actual result proved later in the paper. Patch [H6] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C58] Proposition 5.4 (prop:conditional), lines 857–860 (applied 2026-11-10 with the author's approval)
The same conull event is still simultaneous in all `z`; only `T` is allowed to depend on the sample and the center. Patch [H7] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C59] Theorem 5.5 proof, lines 955–1013 (applied 2026-11-10 with the author's approval)
This is the one non-surgical patch: it replaces the fixed-center law argument by the pathwise covariance already used later in correction [C50], and it makes the all-center event and two-sided continuity explicit. Patch [H8] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C60] Lemma 5.8 (lemma:strong-compatibility) and Proposition 1.3 locality proof, lines 1020–1046 (applied 2026-11-10 with the author's approval)
This keeps Proposition 1.3 for every deterministic open `U`; only the auxiliary domain-cluster lemma is restricted to the regular domains actually used in the exhaustion. Patch [H9] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C61] Lemma 6.4 (lemma:annulus-hit), lines 1189–1194 and 1207–1208 (applied 2026-11-10 with the author's approval)
Audit R1 extension (z3, commit 04195351; marker at corrected:1247): `a = a(b,p,\gamma,\boldsymbol{\alpha}_0)`; the transfer uses the exact Weyl density, so no `C_1/C_2` ratio remains (audit R2: the earlier email formula was wrong); the factor `|z|^{-\boldsymbol{\alpha}_0\gamma}` is replaced by the sup/inf ratio over the annulus, at most `1001^{\gamma|\boldsymbol{\alpha}_0|}`, giving `a = a'/1001^{\gamma|\boldsymbol{\alpha}_0|}`.
No dependence on `r` or `z` is introduced; only the fixed insertion parameter must be displayed. Patch [H10] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C62] Lemma 6.7 (lemma:very-good-annuli-hit), lines 1311–1319 (applied 2026-11-10 with the author's approval)
If `\beta^-` is fixed once and for all as a function of `\gamma`, its displayed dependence may be suppressed; the `\boldsymbol{\alpha}_0` dependence may not be presented as uniform. Patch [H11] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C63] Lemma 6.9 (lemma:harmonic-odometer-comparison), lines 1463–1471 and line 1490 (applied 2026-11-10 with the author's approval)
This excludes exactly the false `\infty\cdot0` case; all later applications have a finite comparison supremum. Patch [H12] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C64] Lemma 6.13 (lemma:low-mass-implies-small-odometer), lines 1714–1716 (applied 2026-11-10 with the author's approval)
The paper may retain the single universal `C_3` supplied by Lemma 6.6; Lean’s stronger “every `C_3>0`” version need not be printed. Patch [H13] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C65] Appendix A setup, equation eq:volume-growth, lines 4131–4135 (applied 2026-11-10 with the author's approval)
Audit R1 (z3, commit 04195351; marker at corrected:4192 and at the volume-growth hunk): `\appendix` restored (audit A1, unmarked damage of the [C44]/[C65] hunks), and the sentence deleted in this hunk restored, citing Lemma 2.4 of the corrected draft (audit A2).
This is the exponent pair used by the formal statement and by the LQG volume bounds cited earlier. Patch [H14] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C66] Appendix A obstacle and supersolution class, lines 4155–4164 (applied 2026-11-10 with the author's approval)
The off-pole formulation is equivalent to majorization of the `-\infty` obstacle and matches the formal admissible class. Patch [H15] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C67] Appendix A.5 (lemma:appendix-conservation-of-mass), lines 4394–4396 (applied 2026-11-10 with the author's approval)
The proof already uses `\mu` throughout, so no proof edit is needed. Patch [H16] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C68] Appendix A.6 (lemma:appendix-cluster-compatibility), lines 4457–4465 (applied 2026-11-10 with the author's approval)
This is the exact deterministic quantifier order audited in chat 210; the rest of the proof is unchanged. Patch [H17] of ChatGPT chat 248 (notes/fp-gaps/CHATGPT-248-hb-pending-latex-patches-H1-H21-PRO.md), from the Pro audits of chats 164 (Section 5), 203 (Section 6), 204 (Sections 2-4, Appendix A) and 210 (Appendix A).

## [C69] Standing dependence on alpha_0 (Prop 6.1, Lemma 6.3, Lemma 6.7, Lemma 6.11, Prop 7.2, Lemma 10.1), corrected:389 (audit A5; z3, commit 04195351)
Printed: the constants were stated or justified as depending only on `\gamma`, although by Lemma 2.4 and Lemma 6.4 they depend on `\boldsymbol{\alpha}_0`. Corrected: one standing convention, with the dependence written out at each site. Bookkeeping, minor; email: Part 2.

## [C70] Proposition 11.2 (eq:mass-times), corrected:3061 (audit A6; z3, commit 04195351)
Residual (audit R2): measurability of the cone-condition set `A` (corr:3065) is not yet proved; the email says so.
Printed: the passage from intervals to all Lebesgue measurable sets was a "standard machine" argument. `A \mapsto \mu_h(\bigcup_{t\in A}\partial\regcluster{}{t})` is not additive, and the interval computation gives only an inclusion up to a null set (GRAPH G37). Corrected: for every Lebesgue measurable `A`, eq:mass-times is the boundary-union identity of Section 11, proved by arrival times (the [C46] argument). Evidence: GRAPH G37.

## Early corrections [C1]-[C36] (applied 2026-11-10 with the author's approval, lh 23:58 UTC)
Only the adopted early corrections that are genuine printed errors are patched below. Each patch keeps the original label `n` and is marked by a trailing `% CORRECTION [Cn]` comment on the modified line. Superseded items and the items not adopted are listed at the end.

## [C1] Lemma 2.4 (lemma:volume-growth), line 502 (early correction; applied 2026-11-10 with the author's approval)
Printed: `\beta^+ \in (0,(2-\gamma)^2/2)` and `\beta^- > (2+\gamma)^2/2` for every `\boldsymbol{\alpha}_0`. Corrected: `\beta^+ \in (0,\min\{(2-\gamma)^2/2,\gamma(Q-\boldsymbol{\alpha}_0)\})` and `\beta^- > \max\{(2+\gamma)^2/2,\gamma(Q-\boldsymbol{\alpha}_0)\}`. Reason: at `z=0`, `\log\mu_h(B_\epsilon(0))/\log\epsilon \to \gamma(Q-\boldsymbol{\alpha}_0)`, so the printed upper bound fails for `\boldsymbol{\alpha}_0>2` and the lower bound for `\boldsymbol{\alpha}_0<-2`, both admissible since `\boldsymbol{\alpha}_0\in(-\infty,Q)`. Evidence: ESCALATIONS E1; CORRECTIONS-PROPOSED [C1].

## [C3] Section 3, equations (3.3) and (3.4) (eq:non-co-set, eq:limit-odometer), lines 597 and 601 (early correction; applied 2026-11-10 with the author's approval)
Printed: the cluster uses `G_{B_r;z}(z,x)` and the odometer uses `t G_{B_r;z}(0,\cdot)`. Corrected: `G_{B_r}(z,x)` and `t G_{B_r}(z,\cdot)`. Reason: the Green function is that of `B_r` with pole at `z`; Lemma 3.2 (`\Delta u = -t\delta_z + \dots`) requires the pole at `z`. Evidence: CORRECTIONS-PROPOSED [C3].

## [C5] Equation (2.13) (eq:defining-property-of-kernel), line 551 (between Proposition 2.5, prop:lbm-exit-time, and Proposition 2.6, prop:lbm-continuity) (early correction; applied 2026-11-10 with the author's approval)
Printed: `\P[\mathcal B^x_t \in dy \mid h] = p^K_t(x,y)\,dy`. Corrected: `p^K_t(x,y)\,\mu_h(dy)`. Reason: the law of the LBM at a fixed time is absolutely continuous with respect to `\mu_h`, which is singular with respect to Lebesgue measure. Evidence: ESCALATIONS E5; CORRECTIONS-PROPOSED [C5].

## [C6] Theorem 1.1(a) (theorem:harmonic-balls), line 160 (early correction; applied 2026-11-10 with the author's approval)
Printed: `\mu_h(\partial\Lambda_t(x)) = 0`. Corrected: `\mu_h(\partial\Lambda_t(z)) = 0`. Reason: `x` is not bound in the statement; `z` is the centre of the family. Evidence: CORRECTIONS-PROPOSED [C6].

## [C7] Section 1, harmonic-ball test class (eq:harmonic-ball, Theorem 1.1), line 150 (early correction; applied 2026-11-10 with the author's approval)
Printed: `f_2 \in \tilde H_O(\Lambda(z))` for some `O` with `\Lambda(z)\subset\overline O`. Corrected: for some bounded open `O` with `\overline{\Lambda(z)}\subset O`. Reason: with the printed class, a bounded open `\Lambda` containing `z` need not be a harmonic ball; the test function `G_O(\cdot,y)` with a pole `y\in\partial\Lambda` is admissible and gives a contradiction (Lebesgue and `\mu_h` counterexample). Evidence: CORRECTIONS-PROPOSED [C7] (Lean-certified, commit dd688d2).

## [C12] Definition 11.1 (def:lipschitz), line 2874 (early correction; applied 2026-11-10 with the author's approval)
Printed: `U \cap B_r(x_0) = \{ z \in B_r(x_0) : \Im(z) > f(\Re(z)) \}`, where `U` is not defined in the definition. Corrected: `A \cap B_r(x_0)`. Reason: typo; `A` is the set being defined. Evidence: CORRECTIONS-PROPOSED [C12].

## [C18] Proposition 7.2 (prop:continuity-of-clusters), line 2092 (early correction; applied 2026-11-10 with the author's approval)
Printed: `\cluster{z}{t+\epsilon} \Subset \cluster{z}{t} + B_\delta(z)`. Corrected: `\cluster{z}{t} + B_\delta`, the ordinary `\delta`-neighbourhood, as in Proposition 5.2 ([C56]). Reason: for `z\neq0` the translated ball `\Lambda + B_\delta(z)` does not contain the cluster's neighbourhood at small `t` (eq:contains-origin). Evidence: CORRECTIONS-PROPOSED [C18]; commit f92316c.

## [C22] Section 9.2, introduction to Lemma 9.3 (lemma:contains-boundary), line 2405 (early correction tied to [C7]; applied 2026-11-10 with the author's approval)
Printed: harmonic ball "(in the sense of eq:harmonic-ball)". Corrected: "(in the sense of Theorem 1.1)", with the class of the corrected Theorem 1.1 ([C7]). Reason: with the printed narrow class, Lemma 9.1(2) and Lemma 9.3 fail (narrow harmonic balls with Lebesgue `\mu`). Evidence: CORRECTIONS-PROPOSED [C22].

## [C23] Equation (6.2) (good-annulus event, §6.1, eq:good-annulus-harmonic) and the proof of Lemma 6.4 (lemma:annulus-hit), lines 1179-1180 and 1309 (early correction; applied 2026-11-10 with the author's approval)
Printed: "`\mathcal B^u` exits `\A` before exiting `Y`" with `Y \subset \A`. Corrected: "exits `\A` no later than exiting `Y`", i.e. `\tau_\A \le \tau_Y`. Reason: with `Y \subset \A`, `\tau_Y \le \tau_\A`, so the strict reading has probability 0 and the event is trivial; the intended event is `\tau_\A \le \tau_Y`, the reading used in `Defs/Annuli.lean`. Evidence: docs/campaign/cex/AlphaUniformity.md section 2, step 1; CORRECTIONS-PROPOSED [C23].
- [C71] Theorem 5.5 (two-sided Hausdorff continuity of the global cluster family), proof: the left-continuity step is made
  explicit (missing detail, not an error; MQ-lh-24, CODEX PARTIAL 13:45Z). Printed: the proof passes from right-continuity
  (Proposition 5.4) to two-sided continuity with "by Proposition 5.4" only. Corrected: the three-line argument of MQ-lh-24
  (left-continuity from exact mass, full support of `mu_h`, openness and monotonicity, then compactness). The statement is
  unchanged; Theorem 1.1(b) and [C59] stay as printed (TRUE, CODEX). Patch: `% CORRECTION [C71]` at the M4 comment of the tex.

## Early items: superseded or not adopted (no separate patch)
- Superseded by a later patch that makes the same correction: [C2] by [C65]; [C4] by [C53] and [C67]; [C8] by [C55]; [C9] by [C58]; [C10] by [C51] (the weak form `\cluster \subset A` is part of [C51]); [C11] by [C43]; [C13] by [C52]; [C14] by [C54] and [C68]; [C15] by [C64]; [C16] by [C49]; [C19] by [C57]; [C20] by [C58]; [C21] by [C60]; [C24] by [C63] (finite-supremum premise); [C25] by [C61] (`a(b,p,\gamma,\boldsymbol{\alpha}_0)`; the `a(b,\gamma)` of Lemma 6.3 is true, AlphaUniformity.md section 6); [C26] by [C62].
- Not adopted: [C17] as a proof-gap item (operator 04:35); its statement generalisation (Lemma 11.12 for all `α₀ < Q`) is adopted as [C43] (operator E13), so [C17] and [C43] agree only through [C43] (audit R2).
- No record found: [C27]-[C36] (no analysis in CORRECTIONS-PROPOSED.md, FROZEN.md, ESCALATIONS.md, GAPS-HB-1106.md or cex/).

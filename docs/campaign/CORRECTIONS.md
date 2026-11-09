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
- [C44] Pinch positive-probability proof: replace the original bump construction by local certificates and the joint large-mass/small-diameter construction; the printed shrinking factor and support/strictness estimates do not suffice.
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

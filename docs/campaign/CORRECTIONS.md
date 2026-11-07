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

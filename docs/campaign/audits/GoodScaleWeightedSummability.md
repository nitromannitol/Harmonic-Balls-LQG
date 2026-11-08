# Good-scale weighted summability

Task: `good-scale-singular-weight-summability`.

The deterministic estimates in `notes/sec11-proof/sec11-proof-r10.tex:528-581`
are formalized in `HarmonicBalls/Proofs/Metric/GoodScaleWeightedSummability.lean`.
`goodScaleLength` is exactly `M * 2^(-ξ Q nᵢ) * exp(ξ b(nᵢ))`.
`goodScaleWeightedLength` multiplies `2 * goodScaleLength` by the exact inner
radius power for `0 ≤ α`, and by the exact outer radius power for `α < 0`.

`summable_goodScaleLength` proves summability when `ξ,Q > 0`, `i ≤ nᵢ`,
and `b(n)/n → 0`. `summable_goodScaleWeightedLength` additionally assumes
`α < Q` and `nᵢ₊₁/nᵢ → 1`, and proves summability for both insertion signs.
The ratio uses total real division, allowing a zero initial scale. The results
allow arbitrary real `M`, so in particular apply to the positive `M` in the
source; they do not require strict increase or a bound on absolute gaps.

The common helper proves summability by comparing the exponential with a
geometric series after its normalized logarithmic rate is shown negative.
The selected errors are sublinear by composition with `nᵢ → ∞`. No metric
moment, independence, or additional literature input is assumed, and this
deterministic helper is not a numbered-result closure. Both principal theorems
print only `propext`, `Classical.choice`, and `Quot.sound`.

# Positivity of the LQG metric Weyl exponent

`IsLQGMetric.weylExponent_pos` in `HarmonicBalls/Proofs/GFF/MetricXiSign.lean` proves `0 < ξ` from `IsLQGMetric γ ξ 𝔇` and `0 < γ`; it does not require `γ < 2` or any new hypothesis. It uses Leonardo Bonanno's construction through `exists_projectWholePlaneGFF` to rule out a vacuous metric axiom.

The fixed-distance law comes from the measurable observable decoder and affine invariance. For `rₙ = exp (-n)`, `Bₙ = hcirc rₙ 0`, `Xₙ = 𝔇 (hC) 0 rₙ`, and the normalized affine distance `Yₙ`, the proof establishes:

- `Yₙ` has the fixed law of `𝔇 (hC) 0 1`, which is almost surely positive.
- `E[Bₙ²] = n` and `Bₙ/n → 0` in probability, using Chebyshev's inequality.
- `log(Yₙ)/n → 0` in probability by fixed-law tightness, without independence.
- `Xₙ → 0` almost surely and in probability, and for each n, almost surely, `Xₙ = exp (ξ * (Bₙ - lqgQ γ * n)) * Yₙ`.

For nonnegativity, the proof intersects the countable families of positive-distance and scaling events, takes successive subsequences with almost-sure convergence for both probability limits, and uses the resulting log-distance limit together with the eventual inequality `Xₙ < 1`. It excludes `ξ = 0` separately: the scaling identity gives the fixed positive distance law for `Xₙ`, contradicting convergence to zero in probability. No simultaneous raw distribution representation or physical-dimension identification is used.

# Radial circle-average increments

For positive radii `r ≤ s`, the increment `h_r(0) - h_s(0)` is centered Gaussian with variance `log (s / r)`. The result is valid for `r = s`, where the variance vanishes, and in fact imposes no upper bound on `s`.

The cross-covariance is computed from the four terms in `covariance_concentric_increments`: when `r ≤ s ≤ u ≤ v`, the maximum expressions cancel. The finite-family theorem applies joint Gaussianity of the increments and the zero-covariance criterion. The arbitrary-index theorem then uses the finite-subfamily characterization of independence. The separation condition allows touching endpoints and zero-length intervals; the result does not assume a Brownian-motion identification.

For `0 < q ≤ 1`, increments between radii `q^(n+1)` and `q^n` form an independent sequence, each with centered Gaussian law of variance `-log q`. The case `q = 1` is included. The import closure includes Leonardo Bonanno's LatticeProb work.

The Lean file prints the axioms of every exported theorem. All lists contain only `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-token scan is clean.

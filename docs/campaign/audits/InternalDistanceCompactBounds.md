# Internal distance on compact subsets

The declarations in `HarmonicBalls/Proofs/Metric/InternalDistanceCompactBounds.lean`
use only `IsEuclideanLengthMetric D`, an open connected domain `U`, and, for
the uniform estimate, a compact subset `K ⊆ U`. They establish local equality
with `ENNReal.ofReal (D x y)`, finiteness for `x, y ∈ U`, and finiteness of
`⨆ x ∈ K, ⨆ y ∈ K, internalMetric D U x y`. The last statement also covers
empty `K`. No extra nonnegativity assumption is needed: it follows from
symmetry and the triangle inequality.

The proofs reuse existing project results. `InternalMetricNear.lean` proves
the local comparison by controlling the length of paths which leave `U`.
`PinchConstrainedFiniteness.lean` obtains finiteness along an arbitrary path
in `U` by a finite chain of locally short edges; a connected open subset of
`ℂ` is path connected. The same file combines continuity with compactness for
a fixed basepoint. `PinchDiameterFiniteness.lean` uses the triangle inequality
to obtain the two-point compact bound. None of these steps assumes that the
ambient metric is complete, proper, or geodesic, or that Euclidean paths are
rectifiable in that metric.

These are deterministic metric statements; they assert neither a tail bound
nor an around-annulus loop. They use no new literature input or numbered-result
closure. The implementation consumes the project's existing metric API and
mathlib; no Lattice-Probability result is used.

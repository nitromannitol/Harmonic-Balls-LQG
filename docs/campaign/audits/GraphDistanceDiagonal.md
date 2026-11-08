# Diagonal graph-distance audit

Leonardo Bonanno contributed to the graph-distance formalization.

For a locally finite measure `μ` with `μ {z} = 0`, the module proves that
`liouvilleGraphDistance μ ε z z = 1` for `ε > 0`, every dyadic exponent is
zero, and `IsLiouvilleGraphDimension μ z z d` is false for every real `d`.
The small-ball argument uses only the null singleton at `z`; no global
nonatomicity or literature input is assumed.

The corrected harmonic-balls paper defines `d_γ` through the Hausdorff
dimension of the LQG metric space (lines 424–426), not through a diagonal
point-to-point graph exponent. The frozen physical-dimension predicate uses
the distinct points 0 and 1 (Defs/LQGGraphDistance.lean:97–102).

Source-scope observation: Ding and Gwynne, arXiv:1807.01072v3, Definition 1.3
and Theorem 1.4, p. 6, equation (1.8), print the point-to-point assertion for
each `z, w ∈ ℂ` without an explicit distinctness condition. Their cover
allows the constant path and a single small-mass ball when `z = w`; for a
locally finite measure null at that point, its exponent is zero, whereas the
printed right side is positive. This indicates a missing distinct-endpoint
restriction in that printed point-to-point assertion; it does not challenge
the physical dimension predicate using 0 and 1. The neighboring Theorem 1.5
explicitly specifies distinct points. See
https://arxiv.org/pdf/1807.01072, p. 6.

The local check and module build pass. Printed axioms for all three declarations
are `propext`, `Classical.choice`, and `Quot.sound`.

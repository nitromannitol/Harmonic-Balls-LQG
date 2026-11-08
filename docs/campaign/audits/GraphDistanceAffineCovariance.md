# Graph distance under real similarities

`isLiouvilleGraphCover_affine_iff` proves equality of admissible natural cover counts for every real threshold, including nonpositive thresholds, arbitrary measures and endpoints, and every nonzero real scale. The map is `x ↦ (r : ℂ) * x + b`. Balls retain their unrestricted centers and positive radii; their masses are preserved under pushforward. The proof transports paths and covers in both directions using the inverse similarity.

`liouvilleGraphDistance_affine` takes the infimum of the same set of counts, so it also covers the infinite-distance case. `isLiouvilleGraphDimension_affine_iff` transfers both eventual finiteness and the dyadic exponent by exact equality, without an LQG coordinate law or a literature hypothesis. These deterministic results do not close a numbered paper result.

The declarations are checked with the project Lean compiler and have only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

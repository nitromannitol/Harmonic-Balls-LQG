# Graph distance under complex similarities

`isLiouvilleGraphCover_complex_similarity_iff` identifies admissible natural cover counts for every measure, real threshold, endpoints, and nonzero complex multiplier. The map is `x ↦ r * x + b`. The proof uses the exact image of each ball, with radius multiplied by `‖r‖`, and transports paths and covers in both directions using the inverse similarity. It follows the real-affine proof and acknowledges Leonardo Bonanno's contributions.

`liouvilleGraphDistance_complex_similarity` identifies the sets used in the infimum, giving equality in `ℕ∞` even when the distance is infinite. `isLiouvilleGraphDimension_complex_similarity_iff` transfers eventual finiteness and the dyadic exponent using this exact equality. No LQG coordinate law or literature hypothesis is used, and these deterministic results do not close a numbered paper result.

The three declarations have only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

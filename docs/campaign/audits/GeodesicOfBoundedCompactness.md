# Geodesics from boundedness

`HarmonicBalls/Proofs/Metric/GeodesicOfBoundedCompactness.lean` proves a deterministic bridge for `IsEuclideanLengthMetric D`. If each set contained in some `D`-closed ball is bounded in the Euclidean metric, `IsEuclideanLengthMetric.exists_geodesic_of_bounded_sets` constructs a Euclidean-continuous path `p` from any `x` to any `y` with `D (p s) (p t) = |s - t| * D x y` on `[0, 1]`. The intermediate theorem `exists_geodesic_of_isBounded_closedBalls` uses the equivalent restricted hypothesis that each `D`-closed ball is Euclidean bounded.

The existing Euclidean continuity of `D x ·` makes each `D`-closed ball Euclidean closed. Mathlib's Heine–Borel theorem makes it compact under the boundedness hypothesis. The proof then uses `IsEuclideanLengthMetric.exists_geodesic_of_compact_closedBalls`, the existing compactness and midpoint construction. Nonnegativity of `D` follows from symmetry, the triangle inequality and the zero diagonal; it is not an additional hypothesis. The boundedness premise is deterministic and is not claimed for an LQG metric here.

The file uses existing formalization infrastructure and acknowledges Leonardo Bonanno. It introduces no literature input and does not claim closure of a numbered result. The three printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

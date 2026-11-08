# Small weighted paths: deterministic construction

Task: `deterministic-small-weighted-paths-from-diameter-bounds`.

The exact target is `SmallWeightedPathExistence` in
`HarmonicBalls/Proofs/Metric/SmallWeightedPaths.lean`, proved by
`IsEuclideanLengthMetric.smallWeightedPathExistence`. It assumes positive,
strictly decreasing radii converging to zero, positive summable length bounds,
summable prescribed annular costs, and the stated internal-metric bounds.
Its conclusion gives the requested path, containment, avoidance, duration and
weighted-integral inequalities, including the origin and zero duration.

The proof selects a first contact with each inner sphere, uses the internal
distance bound and image-preserving arc-length parametrization to construct
short annular pieces, and bounds each piece's logarithmic cost for either sign
of the exponent. It chooses compatible pieces recursively and concatenates
them with summable original lengths. Each time before the limit lies on a
piece, proving origin avoidance; reversing gives the path from the origin.
For a point inside a later band, nonnegative summable tails are compared with
the tails starting at the prescribed index.

`IsEuclideanLengthMetric.weylScaling_le_smallPathCost_tail` exports the Weyl
bound, and `IsEuclideanLengthMetric.uniform_weylScaling_small_closedBall`
proves the bounds tend to zero uniformly on the shrinking closed balls.
No paths, endpoint connection, final distance bound, or literature input is
assumed as a premise. This establishes the deterministic construction only;
it does not claim any numbered result or singular-metric axiom.

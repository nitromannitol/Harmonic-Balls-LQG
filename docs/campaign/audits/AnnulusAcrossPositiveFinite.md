# Annulus across distances: deterministic audit

Task: `metric-annulus-across-positive-finite`.

The corrected paper defines the open round annulus at lines 336–339,
the internal distance at lines 428–432, and set distance at lines 459–465.
`Proposed/PfefferMetricScaling.lean:52` defines the ambient across distance
as the infimum between the two boundary spheres. The new proof uses this
existing definition only; it assumes no proposed literature proposition.

Existing provider: `Steps/Sec11/PinchDistancePositivity.lean:32`,
`IsEuclideanLengthMetric.setDist_spheres_pos`, proves positivity of the
ordinary ambient set distance. `Steps/Sec11/LocalPathLength.lean:148`
identifies its `ENNReal.ofReal` with the infimum of point distances. Thus the
new `pfefferAcross_pos_lt_top` proves positivity and finiteness for the
actual across observable, with no equivalence to an around distance.

The genuinely additional compact-set theorem
`internalDistance_compact_separated_bounds` applies to any two disjoint
nonempty compact subsets of a connected open set. Its lower bound is the
positive ambient set distance; its finite upper bound is the supremum of
internal distances on their compact union. The annulus specialization
requires `0 ≤ s < r < R < T`, uses the exact open annulus `annulus z s T`,
and includes both boundary spheres. It bounds every pair of internal
distances uniformly and consequently proves positivity and finiteness of their
infimum. The connectedness provider is
`Proofs/Sec6/HarnackIteration.lean:36`.

Each new theorem prints only `propext`, `Classical.choice`, and `Quot.sound`.
No new hypothesis, literature input, or probabilistic scaling law is used.
We acknowledge Leonardo Bonanno's contributions to this formalization.

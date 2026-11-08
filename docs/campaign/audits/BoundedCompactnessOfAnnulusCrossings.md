# Bounded compactness from annulus crossings

Task: `bounded-compactness-from-radial-crossing-bounds`.

`IsEuclideanLengthMetric.isCompact_of_radialCrossing_lowerBounds` proves that
any closed, `D`-bounded subset of the complex plane is compact, assuming
nonnegative inner radii, ordered radial annuli, crossing-length lower bounds,
and divergence of their finite partial sums. Closedness and compactness are
stated in the Euclidean topology, which `IsEuclideanLengthMetric.isOpen_iff`
identifies with the topology induced by `D`. The distance boundedness premise
retains an arbitrary center and real bound.

The existing provider `isBounded_of_radialCrossing_lowerBounds` proves the
Euclidean boundedness needed for Heine–Borel. The new compactness consequence
applies to all closed bounded sets, not only closed balls. The geodesic theorem
uses `exists_geodesic_of_bounded_sets` with that same existing boundedness
provider to construct constant-speed paths between arbitrary points. No extra
completeness premise or probabilistic annulus-growth assertion is introduced.

These are deterministic helper results and do not claim a numbered paper result.
The Lean module acknowledges Leonardo Bonanno and the pinned Lattice-Probability
`lean-v4.35` development. Both declarations print only `propext`,
`Classical.choice`, and `Quot.sound` as axioms.

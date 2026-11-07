# Continuous circle-average versions

`HarmonicBalls/Proofs/GFF/ContinuousCircleVersion.lean` uses Leonardo Bonanno's
continuous circle-average version for the reconstructed normalized GFF. At each
positive radius and center its fixed-coordinate equality follows by combining
Bonanno's result, reconstructed-field normalization, and the existing raw-circle
bridge. Subtracting its own unit-circle value normalizes every sample; that value
is almost surely zero. Coordinate maps are almost everywhere measurable by
agreement with the measurable raw coordinate.

`ae_circle_version_eq_on_countable` intersects the coordinate events for a
specified countable set of positive-radius coordinates.
`ae_continuous_circle_versions_eq` intersects the events at a countable dense
sequence in the positive-radius parameter space, then extends equality by
continuity. It compares two continuous versions; it does not assert raw-circle
agreement at all coordinates on a common event.

All three declarations print only `propext`, `Classical.choice`, and
`Quot.sound` as axioms. No additional literature premise is introduced.

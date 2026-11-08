# Comparable-measure graph dimension audit

The checked declarations in `HarmonicBalls/Proofs/Sec2/GraphDimensionComparableMeasures.lean` use the existing `IsLiouvilleGraphCover`, `liouvilleGraphDistance`, and `IsLiouvilleGraphDimension` without modifying their definitions.

* `IsLiouvilleGraphCover.of_measure_le` and `liouvilleGraphDistance_mono_measure` preserve the direction of measure order and cover all `ℕ∞` distances, including infinity.
* `isLiouvilleGraphDimension_of_measure_sandwich` derives finiteness of the middle distance from the upper distance before applying `ENat.toNat_le_toNat`. It squeezes the full-scale logarithmic exponents using the eventual positivity of the denominator.
* `isLiouvilleGraphDimension_iff_of_comparable` uses the proved positive scaling theorem at both bounds and applies reciprocal scalar bounds for the reverse implication. Both real constants are strictly positive. The conclusion concerns the supplied exponent and fixed points; it makes no identification with the physical LQG dimension.

No literature premise is introduced. The four declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The source contains no `sorry`, `admit`, `axiom`, or `native_decide` declarations.

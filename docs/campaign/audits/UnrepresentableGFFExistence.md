# Unconditional GFF version counterexample

This is E55, a version issue in the project formalization, not a claim that a numbered result of Bou-Rabee and Gwynne is false.

`exists_projectWholePlaneGFF_unrepresentable_modification` starts from `exists_projectWholePlaneGFF` (Leonardo Bonanno's normalized whole-plane GFF construction) and applies the existing product modification theorem. The resulting product measure is a probability measure; both the original field and the modified field satisfy the full six-field `IsWholePlaneGFF` predicate. Circle averages are pulled back along the first projection. For every fixed test function the pairings agree almost surely, with the exceptional set allowed to depend on the test. On one full-measure event the modified sample has no `PlaneDistribution` representing all its test pairings simultaneously.

`exists_projectWholePlaneGFF_ae_unrepresentable` packages the product space as an unconditional witness. `not_exists_ae_simultaneous_representation` excludes any distribution-valued map representing the raw pairings almost surely, without requiring measurability; it therefore excludes measurable maps as well. The fixed-test equivalence does not assert simultaneous equality.

`exists_projectWholePlaneGFF_ae_euclidean_metric_extension` independently applies the existing metric-extension product theorem. Its full-measure event quantifies simultaneously over every current `extendPlaneMetricMap` input and both plane points. The version-aware repair of the underlying definitions remains an operator decision. No frozen declaration or literature assumption is changed.

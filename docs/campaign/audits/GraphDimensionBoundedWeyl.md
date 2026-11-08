# Bounded Weyl perturbation graph dimension audit

`HarmonicBalls/Proofs/Sec2/GraphDimensionBoundedWeyl.lean` retains the existing graph-cover, distance, and dimension definitions. Leonardo Bonanno contributed to this formalization.

* `isLiouvilleGraphDimension_iff_withDensity_exp` bounds the density by the positive constants `exp a` and `exp b`, uses `withDensity_mono` and the proved comparable-measure theorem. The measurable-density assumption is unnecessary for this measure inequality: the conclusion holds for arbitrary `g` with global pointwise bounds.
* `ae_lqgLimit_addCircleAverage_graphDimension` intersects the original LQG-limit event with the GFF dyadic-profile continuity event, then invokes the proved `Section6.isLQGLimit_addCircleAverage`. On that same event it gives the dimension equivalence simultaneously for every globally bounded continuous perturbation, all pairs of points, and all exponents. Absolute-value bounds yield global bounds for `γ * f` without a sign restriction on `γ`.
* The global bounds are essential to this argument for unrestricted covers. No assertion is made about logarithmic insertions, local bounds, or the physical dimension, and no literature premise is introduced.

Both declarations print only `propext`, `Classical.choice`, and `Quot.sound`. The Lean file has no `sorry`, `admit`, `axiom`, or `native_decide` declarations.

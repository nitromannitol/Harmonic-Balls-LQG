# Cylinder mixing extension audit

`HarmonicBalls.tendsto_measure_inter_preimage_iterate_of_cylinderFactorization`
proves the assigned generic statement. The probability measure and the
measure-preserving map use the ambient measurable space. The events use exactly
the sigma-algebra `coordinateSigma X`, the supremum of the coordinate comaps.
The bounded continuous premise explicitly quantifies over both finite coordinate
lists and both test functions. No countability assumption on the index type or
invariance of the generated sigma-algebra under the map is required.

The proof proceeds as follows:

1. Finite-measure sets in the coordinate sigma-algebra are approximated in
   measure by pullbacks of measurable finite-coordinate cylinders, using
   Mathlib's set-ring approximation theorem.
2. Measurable indicators are approximated in L¹ by bounded continuous functions
   clipped to `[0,1]`. A product-error inequality and preservation under each
   iterate extend the assumed convergence to finite-dimensional Borel events.
3. Mathlib cylinders are reindexed by `Fin m`; symmetric-difference estimates
   extend event mixing from those cylinders to the coordinate sigma-algebra.

The proof uses no GFF-specific input. Canonical GFF shift measurability and law,
generation by integral-zero tests, common almost-everywhere versions, and
canonical ergodicity remain separate obligations. In particular this result
alone does not close Lemma 11.12.

Validation: `lc` and `lb HarmonicBalls.Proofs.MeasureTheory.CylinderMixingExtension`
passed. The target's printed axioms are `propext`, `Classical.choice`, and
`Quot.sound`; the forbidden-placeholder scan is clean.

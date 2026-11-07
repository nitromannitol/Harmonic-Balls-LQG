# Transposed Green source truncation

`HarmonicBalls.transposedGreen_source_truncation` proves integrability of every
truncated potential, convergence at almost every observer with source-slice
integrability made explicit, and convergence in the integral L1 norm.

The theorem applies to any increasing measurable exhaustion covering the domain;
compactness and containment of the truncation sets are unnecessary. The source
measure is finite and concentrated almost everywhere on the bounded open domain.
The Green kernel retains source-observer order, with no reciprocity or
Laplacian assumption. Leonardo Bonanno's potential-theoretic infrastructure is
used through the mixed-kernel integrability theorem.

The proof applies Fubini to obtain integrable source slices, source-side
dominated convergence to the measurable indicators, and observer-side dominated
convergence to their potential differences. The reported axioms are the standard
`propext`, `Classical.choice`, and `Quot.sound`.

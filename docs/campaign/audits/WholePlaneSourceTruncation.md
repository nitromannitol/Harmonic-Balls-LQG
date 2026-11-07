# Whole-plane source truncation audit

The source is a finite measure concentrated on a compact set; the measurable
truncation sets increase and their union has full source measure. The theorem
`wholePlane_source_truncation_ae` gives convergence volume-almost everywhere on
all of the plane. `wholePlane_source_truncation_on` gives the corresponding
almost-everywhere convergence and convergence of the integral of the absolute
difference on every bounded observer set, without assuming pointwise kernel
integrability everywhere.

The proof uses the literal source-observer kernel order and its symmetry for
`greenPotential`. Product integrability follows from the logarithmic product
estimate and planar volume growth; dominated convergence is applied first in
the source variable and then in the observer variable, with the integral of
the absolute kernel as a bound. A countable ball exhaustion yields the global
statement. These declarations are analytic helpers, not a numbered-result
closure and introduce no literature assumptions.

The Lean axiom printout lists only `propext`, `Classical.choice`, and
`Quot.sound` for all three declarations. The implementation contains no
`sorry`, `admit`, `axiom`, or `native_decide` declarations.

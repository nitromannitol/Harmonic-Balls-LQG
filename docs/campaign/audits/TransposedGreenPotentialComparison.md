# Transposed Green potential comparison

`HarmonicBalls.transposedGreen_potential_comparison` compares the literal
source-observer Green potentials for nested bounded open domains and ordered
finite sources carried almost everywhere by the smaller domain. It gives
integrability on the ambient domain for all four domain-source combinations,
and a common almost-everywhere observer event with all four source integrals
integrable, nonnegativity, and the comparison. The source-only and domain-only
specializations are also proved.

The proof uses the mixed Green-kernel integrability theorem and pointwise domain
monotonicity, including the totalized diagonal and exterior values. Fubini gives
integrable source slices; integral monotonicity in the integrand and measure
then gives the comparison. No reciprocity or additional literature input is
used. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

The lock-free check and module build pass. Each theorem reports only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`; the Lean file contains no
forbidden proof placeholders or elevated heartbeat setting.

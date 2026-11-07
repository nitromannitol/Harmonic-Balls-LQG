# Weighted transposed Green bound audit

`weighted_transposedGreen_integrable_product` proves mixed integrability for the
actual Green kernel in source-observer order, using the existing product bound
and bounded multiplication.

`weighted_transposedGreen_bound` uses the finite measure with density
`ENNReal.ofReal |f|` and the uniform transposed Green mass bound. Its mass is
the integral of `|f|`. The norm-of-integral inequality gives the claimed
uniform L¹ bound. `tendsto_weighted_transposedGreen_of_L1` applies this bound
to the difference of the source densities, using common almost-everywhere
source-slice integrability to justify subtraction of the Bochner integrals.
The convergence theorem allows each density its own bound, stronger than a
uniform boundedness assumption.

The kernel, diagonal and totalized integrals retain their original definitions.
No literature input or numbered-result closure is added. All three declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

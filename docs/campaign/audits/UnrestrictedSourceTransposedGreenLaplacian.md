# Unrestricted-source transposed Green Laplacian audit

`transposedGreen_integral_restrict_source` identifies the literal potential with
its restricted-source counterpart at every observer, using the vanishing of the
actual Green kernel outside the domain. This equality includes observers where
Bochner integrals are totalized.

`ae_transposedGreen_integrable_unrestricted_source` applies product
integrability and Fubini to the restricted source, then extends source-slice
integrability to the unrestricted measure by exterior vanishing. Both slices
are integrable on the same almost-everywhere event for volume restricted to the
domain. `integrableOn_transposedGreen_unrestricted_source` and
`hasLaplacian_transposedGreen_unrestricted_source` transfer the existing
finite-source results across the pointwise equality. The negative source in the
Laplacian is the restriction of the original measure to the domain.

The kernel, diagonal and totalized integral retain their original definitions.
No literature input or numbered-result closure is added. All four declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

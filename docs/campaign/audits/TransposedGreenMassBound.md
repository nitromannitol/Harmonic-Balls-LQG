# Transposed Green mass bound audit

- `disc_green_volume_row_bound` specializes the already-proved uniform disc Green bound to planar volume using `volumeGrowth_volume`. The existing bound is derived from the disc kernel and quantitative Riesz estimates, not assumed as an input.
- `transposedGreen_mass_bound` uses bounded-domain product integrability and Green domain monotonicity, with the actual source-observer kernel. It exposes integrability in both orders and of the potential, nonnegativity, and the uniform mass estimate.
- `tendsto_transposedGreen_integral_norm_of_mass_tendsto_zero` derives integral-norm convergence by squeezing the nonnegative potentials against that estimate.
- The diagonal and totalized integrals retain their existing definitions. No literature input or numbered-result closure is added.
- Axiom audit: each declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

# Transposed Green-kernel integrability at typical observers

`ae_transposedGreen_integrable_of_local_upper_growth` gives source integrability
of the literal kernel `greenFunction V y x`, Newton-kernel source integrability,
and absence of a source atom at almost every observer in any ball. The source
is finite and carried by a compact set; the bounded open domain need not contain
that compact set. An enclosing disc, its proved Green symmetry, nonnegativity,
and domain monotonicity supply domination. Joint Green measurability supplies
the required source-section measurability. No general-domain reciprocity or
planar almost-everywhere identity is used; observers outside the domain are
included.

`ae_transposedGreen_integrable_of_local_upper_growth_global` extends this to
the whole observation measure by a countable ball cover.
`ae_lqg_transposedGreen_integrable` uses I2 and LQG local finiteness on one
probability-one event, universally quantifying domains and finite compact
sources inside the domain before the source-dependent observation null set.
No equality with a totalized Green potential is asserted.

This analytic helper uses Leonardo Bonanno's potential-theoretic work and
introduces no new literature input or numbered-result closure. The printed
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

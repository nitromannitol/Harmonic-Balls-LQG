# Integrable-density Green observer bound

`HarmonicBalls/Proofs/Potential/IntegrableDensityObserverBound.lean` establishes mixed integrability of the transposed Green kernel for any measurable signed source-integrable density, a uniform row bound, and the resulting observer L¹ bound and L¹ density continuity.

For each positive radius the constant is chosen before the open subdomain, finite source and density. The source is almost everywhere in the subdomain; the observer is locally finite and satisfies local upper ball growth. The proof applies the existing disc row estimate and Green-domain monotonicity, and uses the finite source with density `‖f‖` for mixed integrability. Fubini and the norm integral inequality give the bound. Convergence is in observer L¹; no almost-everywhere convergence is asserted. The kernel is in source-observer order, and no reciprocity or new literature input is used.

This is analytic infrastructure, not closure of a numbered paper result. The potential-theoretic infrastructure uses work of Leonardo Bonanno. All four declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

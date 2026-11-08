# Source-free uniform density convergence

`HarmonicBalls.sigmaFinite_source_free_density_green_local_uniform` proves uniform convergence on any compact subset `L` of the open source-free set `U`, for actual weighted Green integrals against a sigma-finite measure carried almost everywhere by a bounded open planar domain `V`. Each measurable integrable density and the limit vanish almost everywhere on `U`, and convergence is in the integral L¹ metric. The source is the first kernel argument (`greenFunction V y x`), with the existing diagonal convention.

The preceding bound uses the existing uniform Green kernel bound outside `U`, while the density vanishes almost everywhere inside `U`. The existing sigma-finite source-free harmonicity result provides Bochner integrability at each observer, permitting subtraction of the actual integrals. The uniform bound by the L¹ difference gives the convergence. No reciprocity, boundary assertion, or new literature input is used. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

The standalone Lean check passed. The printed axioms are `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-code scan is clean.

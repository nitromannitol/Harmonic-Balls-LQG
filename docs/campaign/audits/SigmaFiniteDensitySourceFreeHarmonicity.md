# Sigma-finite density source-free harmonicity

`HarmonicBalls.sigmaFinite_integrable_density_transposedGreen_source_free` establishes pointwise Bochner integrability and harmonicity on an open source-free set `U` inside a bounded open planar domain `V`. The measurable signed density is integrable against a sigma-finite measure carried almost everywhere by `V` and vanishes almost everywhere on `U`. The kernel is `greenFunction V y x`, with source `y` and observer `x`, retaining the existing diagonal convention.

The positive and negative density measures are finite by integrability, vanish on `U`, and are carried by `V`. The finite-source uniform Green bound yields integrability at each observer in `U`; change of measure identifies the actual weighted integral with the difference of the two finite-source integrals there. The finite-source harmonicity theorem and this neighborhood identity give the conclusion. No reciprocity or new literature input is used. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

The standalone Lean check passed. The theorem's printed axioms are `propext`, `Classical.choice`, and `Quot.sound`; the forbidden-code scan is clean.

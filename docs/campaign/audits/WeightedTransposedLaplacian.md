# Weighted transposed Green-potential Laplacian

The declarations in `HarmonicBalls/Proofs/Potential/WeightedTransposedLaplacian.lean` are potential-theoretic helpers and do not close a numbered result. The infrastructure uses work of Leonardo Bonanno.

For a bounded open domain and a finite source concentrated almost everywhere in it, `weighted_transposedGreen_slice` proves integrability over the domain of the weighted potential, integrability of its source slices on a common full-volume event, and identification with the difference of the potentials of `positiveSource` and `negativeSource`. The measures inherit concentration by absolute continuity. The density formula and integrable subtraction preserve the literal `greenFunction V y x` order, including its diagonal values; compact source support and reciprocity are not assumed.

`hasLaplacian_weighted_transposedGreen` gives the same integrability and slice identity along with `HasLaplacian` on the domain, with `negativeSource` in the positive measure slot and `positiveSource` in the negative slot. This follows by subtracting the established finite positive-source identities and transferring the result across the almost-everywhere equality. No new literature input is introduced.

Verification: the lock-free Lean check and project module build pass. All three declarations print only `propext`, `Classical.choice`, and `Quot.sound`; the Lean file has no forbidden proof placeholders or heartbeat override.

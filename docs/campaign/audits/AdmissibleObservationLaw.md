# Admissible observation law

Task: `gff-admissible-observation-law-uniqueness`.

The observation map has domain the underlying sample space and codomain
`GFFObservable.Admissible → ℝ`, with its product measurable space. Each
coordinate is measurable by the corresponding pairing or circle-average field
of `IsWholePlaneGFF`; `measurable_pi_iff` gives the full map.

For two realizations on potentially different measurable spaces, the existing
`IsWholePlaneGFF.identDistrib_finite_observables` proves equality of every
finite-coordinate law from joint Gaussianity, zero means, and the same
`wholePlaneGFFCov`. `isProjectiveLimit_map` and projective-limit uniqueness
then give equality of the full pushforward measures. No extra literature
assumption is introduced. The conclusion concerns admissible deterministic
observations only and asserts no simultaneous samplewise representation.

The finite-dimensional proof is in `HarmonicBalls/Proofs/Sec5/GaussianProcessLaw.lean`;
the project also uses Leonardo Bonanno's GFF formalization. The declarations'
printed axioms are `propext`, `Classical.choice`, and `Quot.sound` only.

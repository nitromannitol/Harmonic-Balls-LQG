# General-domain transposed finite-source Laplacian

`HarmonicBalls/Proofs/Potential/GeneralDomainTransposedFiniteSourceLaplacian.lean`
proves `hasLaplacian_generalDomain_transposedGreenPotential`: for a bounded
open planar domain and a finite measure concentrated there, the literal
transposed Green potential has distributional Laplacian minus that measure.
The statement includes atomic sources and uses the totalized Green kernel and
Bochner integral.

The proof bounds the test-function Laplacian on a disc containing the domain,
uses the general-domain product integrability theorem for Fubini, removes the
outside-domain contribution using test-function support, and applies the
bounded-domain fixed-pole Laplacian identity almost everywhere in the source.
No reciprocity or additional literature hypothesis is used. This is an analytic
helper, not a numbered-result closure.

The declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

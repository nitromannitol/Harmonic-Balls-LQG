# General-domain Green product integrability

`HarmonicBalls/Proofs/Potential/GeneralDomainGreenProductIntegrability.lean`
proves product integrability for a finite measure concentrated in a bounded open
planar set, and integrability and local integrability on the set of the literal
transposed potential `x ↦ ∫ y, greenFunction V y x ∂ν`.

The proof encloses the domain in a disc, restricts the existing disc product
estimate, and applies joint measurability and domain monotonicity. Fubini yields
the transposed potential result. No reciprocity, fixed-pole Laplacian, or new
literature hypothesis is used. The concentration assumption is weaker than
compact concentration. This is an analytic leaf, not a numbered-result closure.

The declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

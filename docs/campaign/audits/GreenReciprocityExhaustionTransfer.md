# Green reciprocity: finite-disc exhaustion transfer

`HarmonicBalls/Proofs/Potential/GreenReciprocityExhaustionTransfer.lean`
proves `HarmonicBalls.greenFunction_reciprocity_of_finite_disc_reciprocity`.
Its displayed premise assumes symmetry for every finite union of positive-radius
open discs, including overlapping discs. The indexing set `A` is an arbitrary
subset of the plane, so the premise covers arbitrary finite families of planar
centres. It is neither declared as a literature input nor proved here.

For two distinct points in a bounded open set, the proof uses
`exists_finite_disc_open_exhaustion` and
`tendsto_greenFunction_of_exhaustion` in both orders, followed by uniqueness
of limits. On the diagonal, symmetry is reflexive; if either point is outside,
both sides vanish by the prescribed exterior values. This also covers empty
and disconnected domains. The underlying sweeping and exhaustion work uses
the potential-theoretic infrastructure of Leonardo Bonanno.

The remaining substantive obligation is reciprocity for finite unions of discs,
particularly overlapping discs (E51); no unconditional general-domain
reciprocity or numbered paper-result closure is claimed. The declaration has
only `propext`, `Classical.choice`, and `Quot.sound` as printed axioms.
Both the lock-free check and the module build pass.

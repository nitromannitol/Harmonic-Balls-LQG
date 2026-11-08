# Finite-disc Green reciprocity: proof audit

The proof uses the potential-theoretic infrastructure of Leonardo Bonanno.
`HarmonicBalls/Proofs/Potential/FiniteDiscGreenReciprocity.lean` proves
`greenFunction_finite_discs_comm` for arbitrary finite families of discs,
including overlaps, tangencies, diagonal values, and exterior values. It supplies
this result to `greenFunction_reciprocity_of_finite_disc_reciprocity`, obtaining
`greenFunction_bounded_open_comm` for every bounded open planar set. No
reciprocity assumption or additional literature premise is introduced.

The proof first establishes the circle mean-value property in the pole variable
for the harmonic correction by applying the previously proved balayage identity
to normalized angular measure. The converse mean-value result gives
`harmonicOnNhd_greenHarmonicCorrection_pole` on any bounded open domain.
For a fixed observation y, nonnegativity of the Green function shows that this
correction, as a function of the pole x, is a harmonic minorant of the
Newtonian kernel with pole y. At x = y the kernel is top, so the minorant
bound also holds there. Maximality of the harmonic minorant bounds the
correction by its transpose. Swapping x and y gives equality. Conversion from
extended-real to real values uses the finite Newtonian upper bound off the
diagonal. The symmetry of the Newtonian kernel gives Green reciprocity; its
specified diagonal and exterior values are handled separately.

This argument proves the stronger intermediate theorem
`greenFunction_bounded_open_comm_of_harmonic_minorants`. Applying it to finite
unions proves the exact premise needed by the existing exhaustion transfer,
which is then invoked in `greenFunction_bounded_open_comm`. No boundary
regularity is assumed. In particular, the irregular four-disc example
`four_disc_union_irregular_boundary` is not excluded by the proof.

The lock-free file check and the module build are run for the final file.
Lean's printed axioms for the finite-disc theorem and exhaustion result are
`propext`, `Classical.choice`, and `Quot.sound` only.

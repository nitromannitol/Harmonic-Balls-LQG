# Integrable-density transposed Green diagonal cutoff

`HarmonicBalls/Proofs/Potential/IntegrableDensityDiagonalCutoff.lean` proves product and slice integrability, product L¹ convergence, almost-everywhere convergence of literal source integrals, and observer L¹ convergence for distance cutoffs of the signed weighted Green kernel. It also supplies integrability of the observer potentials.

The source is finite and almost everywhere in the bounded open planar domain, and the measurable signed density is source-integrable. The proof uses the integrable weighted kernel as dominator. Away from the diagonal the cutoff is eventually one; on the diagonal the defined Green kernel is zero. The Green kernel remains in source-observer order. No nonatomicity, boundedness of the density, reciprocity, or extra literature premise is assumed. The cutoff sequence is only required to converge to zero, a stronger result than requiring it to be positive.

This is analytic infrastructure and does not close a numbered paper result. The potential-theoretic infrastructure uses work of Leonardo Bonanno. The declaration prints only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

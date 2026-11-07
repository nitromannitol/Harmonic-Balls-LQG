# Integrable-density transposed Green exhaustion

`HarmonicBalls/Proofs/Potential/IntegrableDensityDomainExhaustion.lean` proves almost-everywhere convergence and integral-norm convergence of the literal weighted transposed Green potentials on a bounded open planar domain along a monotone open exhaustion. It also proves integral-norm convergence when the measurable integrable densities vary and converge in source L¹.

The source is finite and almost everywhere in the limiting domain; it need not be concentrated in any exhaustion member. Each kernel is integrated over the entire source measure, and the observer measure is volume restricted to the entire limiting domain. The proof dominates each smaller-domain kernel by the limiting kernel, uses product and slice integrability on the full product, and applies dominated convergence. The varying-density estimate uses a common row-mass bound on the limiting domain and the triangle inequality. The source argument of the Green kernel remains first, including on the diagonal; no reciprocity or boundary regularity is assumed.

The results are analytic infrastructure for E51 and do not close E51 or a numbered paper result. The potential-theoretic infrastructure uses work of Leonardo Bonanno. The declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

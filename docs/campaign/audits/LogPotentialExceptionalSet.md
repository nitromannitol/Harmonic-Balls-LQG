# Logarithmic potential exceptional set

`ae_logPotential_of_local_upper_growth` in
`HarmonicBalls/Proofs/Potential/LogPotentialExceptionalSet.lean` proves the
logarithmic exceptional-set bridge. For locally finite μ, assume that on each
positive-radius ball μ satisfies a positive-power upper growth bound at small
radii. If finite ν is concentrated on compact K, then on every ball restriction
of μ, almost every x has all of the following properties:

* `Integrable (newtonKernel x) ν` and `ν {x} = 0`;
* the positive and negative lower integrals of `newtonKernelEReal x` are finite;
* their difference, `extendedSignedIntegral`, equals the real Bochner integral.

`ae_logPotential_of_volumeGrowth` gives the same conclusion assuming the
existing `VolumeGrowth` condition on each positive-radius ball. It uses only its
upper bound. The proof chooses a common ball containing K and the ball used for
the μ restriction, applies the existing layer-cake Riesz estimate, obtains a
uniform bound and then product integrability by Fubini. A bounded-distance
logarithm estimate gives product integrability of the logarithmic kernel. The
finite real diagonal value is handled independently: volume growth makes μ
atomless, and product Fubini removes ν-atoms at μ-almost every point. An explicit
off-diagonal lower bound on bounded balls is also proved.

This result addresses logarithmic-potential exceptional sets only. It does not
establish arbitrary polar-nullness, Green-kernel exhaustion convergence,
bounded-representative equivalence, or closure of E51's separate Green-kernel
and test-class obligations. The extended signed integral is defined locally as
the difference of the two nonnegative lower integrals; their finiteness is part
of the theorem, so the equality involves no indeterminate infinity subtraction.

# Mean-zero tests away from the origin

`HarmonicBalls.zeroIntegralAwayOriginApproximation` proves the stated
`ZeroIntegralAwayOriginApproximation` proposition for every smooth compactly
supported test of integral zero. One deterministic sequence works for every
normalized whole-plane GFF; each test has integral zero and support away from
zero, and the actual pairing differences converge to zero in second moment.

`exists_zeroIntegral_awayOrigin_pointwise` provides a common compact support,
pointwise convergence off zero, and convergence in planar L². It constructs the
sequence by cutting out a shrinking ball and restoring the mass with a fixed
integral-one smooth test supported away from zero. Dominated convergence proves
the planar L² limit.

`IsWholePlaneGFF.integral_pairing_sub_sq_eq_covariance` identifies the actual
second moment with the covariance energy, using almost-sure linearity rather
than assuming a samplewise linear version. The energy is controlled by planar
L² through Leonardo Bonanno's Schur estimate in pinned Lattice-Probability,
using `Section6.wholePlaneGFFCov_pairing_eq_logCov` for mean-zero tests. The
common compact support fixes a single Schur constant. No covariance or L²
convergence is assumed.

This supplies an input to Lemma 11.12; it is not a numbered-result closure and
does not prove sigma generation, a shift law, or ergodicity.

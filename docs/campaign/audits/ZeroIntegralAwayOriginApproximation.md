# Mean-zero tests away from the origin: work in progress

The file `HarmonicBalls/Proofs/GFF/ZeroIntegralAwayOriginApproximation.lean`
states the intended universal GFF second-moment approximation as
`ZeroIntegralAwayOriginApproximation`. It does not yet prove that proposition.

`exists_zeroIntegral_awayOrigin_pointwise` constructs mean-zero smooth tests,
each with support away from zero and all supports in one compact set, converging
pointwise away from zero. The proof uses a normalized compactly supported bump
and a sequence of shrinking cutoffs; `tendsto_integral_cutout` proves that the
mass-restoring coefficient tends to zero.

Still needed: a uniform bound and convergence of the logarithmic covariance
energies, followed by the centered Gaussian covariance identity for the actual
second moment. No such convergence is assumed by the proved results. This is
not a claim of a numbered-result closure.

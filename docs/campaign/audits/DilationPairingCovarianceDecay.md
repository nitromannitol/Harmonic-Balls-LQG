# Decay of normalized dilation pairing covariance

Task: `normalized-dilation-mean-zero-covariance-decay`.

The covariance in the operator's `notes/sec11-proof/sec11-proof-r10.tex:320-330`
is proved to tend to zero for the actual `affinePairing` of the whole-plane
GFF, with the normalization circle subtraction included. The result is stronger
than the support condition in that argument: the first test may be any smooth
compactly supported test, without even requiring its integral to be zero. The
contracted test must have zero integral.

`covariance_affinePairing_eq_potential` uses the GFF covariance law, symmetry,
and the planar affine change of variables with its squared-norm Jacobian. The
mean-zero assumption cancels the random circle subtraction. With both tests of
integral zero, `covariance_affinePairing_eq_logPotential` explicitly cancels
both one-point normalization terms. `planarLogPotential_eq_integral` identifies
the remaining expression with the double logarithmic kernel integral, in the
reverse order of integration from the operator's display. Its inner logarithmic
integral is integrable by the existing logarithmic-potential results; the outer
one is integrable by compact support and continuity.

The limit uses continuity of the whole-plane covariance potential and dominated
convergence over the fixed compact support of the contracted test. This avoids
needing a pointwise kernel estimate or interchanging singular integrals. It does
not assert an explicit dyadic rate, Gaussian mixing, ergodicity, or a numbered
result closure. The covariance kernel and normalization are from the corrected
paper `paper/lqg_harmonic_ball-corrected.tex:359-368`. The Section 8 imports
use Leonardo Bonanno's LatticeProb formalization of the ergodic theorem.

All four declarations print only `propext`, `Classical.choice`, and `Quot.sound`.
No new literature input is used.

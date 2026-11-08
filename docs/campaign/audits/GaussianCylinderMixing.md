# Gaussian cylinder mixing: partial audit

The results in `HarmonicBalls/Proofs/GFF/GaussianCylinderMixing.lean` are
finite-dimensional. They establish convergence in distribution of centered
Gaussian vectors under entrywise covariance convergence, convergence of their
bounded continuous expectations, and factorization of product tests once
convergence to a product-space limit has been established. The last statement
is conditional on that convergence; it does not assume or establish mixing.
The file also proves convergence to zero of every fixed bilinear combination of
the mixed original/dyadic GFF pairings, using the existing covariance-decay
theorem and integral-zero tests on the dilated side.

Remaining: construct the independent Gaussian product limit from the two
marginal laws; establish covariance convergence to it from fixed marginal
covariances and vanishing mixed covariances; show the actual original/dilated
GFF vectors satisfy joint Gaussianity, centering, and marginal covariance
invariance, and apply the product-test result. No sigma-algebra mixing,
ergodicity, covariance-norm density, or numbered-result closure is claimed.

`LatticeProb.Prob.CameronMartin` and
`LatticeProb.Prob.Scaling.CramerWoldFilter` currently fail to rebuild against
the installed Mathlib API; the file instead uses Mathlib's variance lemmas,
the working `LatticeProb.Prob.Scaling.CramerWold`, and a direct bounded-test
argument. Leonardo Bonanno's Lattice-Probability development supplies the
Cramér–Wold bridge.

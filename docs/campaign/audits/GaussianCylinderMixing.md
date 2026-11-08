# Gaussian cylinder mixing: finite-dimensional audit

`HarmonicBalls/Proofs/GFF/GaussianCylinderMixing.lean` proves convergence in
distribution for centered jointly Gaussian blocks whose marginal covariance
matrices stay fixed and whose mixed covariances tend to zero. The limit uses
independent copies of the two initial marginal vectors on the product
probability space. Bounded continuous product tests then have factorized
limiting expectations.

The GFF specialization proves joint Gaussianity using weighted and recentered
admissible observables, identifies both marginal covariance matrices, and uses
`DilationPairingCovarianceDecay` for the mixed terms. Dilated test functions
are smooth and compactly supported with integral zero; no punctured-support
condition is used. Both the convergence in distribution and expectation
factorization are proved for finite vectors. No sigma-algebra mixing,
ergodicity, covariance-norm density, or numbered-result closure is claimed.

The proof uses Mathlib's variance lemmas and the working
`LatticeProb.Prob.Scaling.CramerWold` module, with a direct bounded-test
argument. Leonardo Bonanno's Lattice-Probability development supplies the
Cramér–Wold bridge. `LatticeProb.Prob.CameronMartin` and
`LatticeProb.Prob.Scaling.CramerWoldFilter` were found to fail rebuilding
against the installed Mathlib API and are not imported here.

The file's printed axiom dependencies are `propext`, `Classical.choice`, and
`Quot.sound`; there are no additional literature assumptions.

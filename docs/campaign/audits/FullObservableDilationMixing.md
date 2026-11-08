# Finite-observable mixing under normalized dilation

`IsWholePlaneGFF.fullObservableDilationCovarianceDecay` proves the mixed
covariance limit for every pair of admissible observables: smooth compactly
supported pairings of arbitrary mass and circle averages of positive radius.
The exact target is `FullObservableDilationCovarianceDecay`. The only field
hypothesis is `IsWholePlaneGFF`; no covariance-decay or representation hypothesis
is introduced.

The proof uses the covariance potential of the fixed observable. Its continuity
comes from compactly supported planar logarithmic potentials or the explicit
log-max circle potential. The two covariance identities in the file express a
normalized dilated pairing or circle in terms of this potential and its
normalizing circle average. Compact-support dominated convergence and joint
continuity of circle averages show that both terms tend to the same value,
with the pairing's total mass as coefficient. The pairing identity uses the
planar affine change of variables and Gaussian covariance linearity; both
identities use the defining GFF covariance in the order which avoids an
unjustified interchange of the two smearing integrals.

`IsWholePlaneGFF.tendstoInDistribution_dyadic_observables` proves joint weak
convergence of any finite original and dilated vectors to independent vectors
on the product space. The weighted, recentered observable family is jointly
Gaussian; affine invariance fixes the two marginal covariance blocks. The
unit-circle normalization holds almost surely and identifies the limiting
second block with the original observables. The bounded-continuous product
expectation factorization is
`IsWholePlaneGFF.tendsto_integral_dyadic_observables_product`.

The relevant source is the normalized whole-plane covariance and observables
in `paper/lqg_harmonic_ball-corrected.tex` lines 355–368, and the mixing
argument at lines 3674–3718; the requested all-observable extension is also
recorded in `~/paper-fleets/hb/notes/sec11-proof/sec11-proof-r10.tex` lines
290–377. The imported Section 8 development uses Leonardo Bonanno's work
through the pinned Lattice-Probability dependency.

This establishes the finite-observable part only. It does not establish sigma
generation, an actual canonical transformation, measure preservation, or
full mixing and ergodicity, and is not a numbered-result closure.

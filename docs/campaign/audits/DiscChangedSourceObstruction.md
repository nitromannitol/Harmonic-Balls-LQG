# Disc changed-source obstruction

`HarmonicBalls.Proofs.Potential.DiscChangedSourceObstruction` proves
`no_changed_source_translatedDisc_for_large_observation`: for an arbitrary
disc `V = ball c R` containing `ball 0 2`, finite positive measures compactly
concentrated in `V`, a positive source vanishing on `ball 0 2`, and a harmonic
correction on `V`, the whole-plane negative Dirac potential cannot agree with
the changed-source expression almost everywhere for
`(volume + Measure.dirac 0).restrict (ball 0 2)`.

The proof transports source-free disc potential continuity by translation. It
derives the local distributional Laplacian from finite-source disc identities,
using the vanishing of the positive source on the observation set. Riesz
uniqueness forces the residual negative source off the origin to vanish there;
restriction preserves finite mass and concentration on the original compact
set. Thus both relevant potentials are continuous at the origin, and the
existing large-observation contradiction applies. The result uses the actual
totalized potential, including at the atom; it does not assume a Riesz identity,
residual continuity, or general bounded-domain reciprocity. It uses the
potential-theoretic infrastructure of Leonardo Bonanno.

This is a disc-only analytic obstruction, not a closure of E51 or a numbered
paper result. `HasBoundedSubharmonicRepresentatives` quantifies over witnesses
on arbitrary bounded open domains, not just discs, and requires a representative
for each frozen-class test. Excluding disc witnesses alone does not exclude all
such witnesses.

Lock-free compile and shared module build pass. All three declarations print
only `propext`, `Classical.choice`, and `Quot.sound`. The Lean file contains no
forbidden proof tokens or heartbeat override.

# Disc finite-source Green potential

`HarmonicBalls.hasLaplacian_disc_greenPotential` proves `HasLaplacian
(greenPotential (ball 0 R) ν) 0 ν (ball 0 R)` for `R > 0` and a finite
measure concentrated almost everywhere on the open disc. This includes every
finite measure concentrated on a compact subset of the disc, and allows atoms.
The distributional sign is `ΔG = -δ`, as in `Defs/Laplacian.lean` and
Proposition 2.3 of the corrected paper.

The proof specializes the existing upper-growth product-integrability theorem to
planar Lebesgue measure, derives integrability of the totalized potential on the
disc, applies Fubini to the tested kernel, and uses `greenFunctionBall` for each
pole. The Bochner integral is used directly; the product integrability justifies
Fubini even where individual source integrals are totalized. The existing
`greenPotential` and Green kernel definitions, including the diagonal value,
are unchanged. The potential-theoretic infrastructure uses work of Leonardo
Bonanno.

The three printed axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`. No literature input or numbered-result closure is introduced.

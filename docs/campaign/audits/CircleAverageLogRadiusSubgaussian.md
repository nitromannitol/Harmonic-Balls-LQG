# Log-radius circle-average sub-Gaussian tails

Task: `circle-average-log-radius-subgaussian-increment-bound`.

For all real log radii `s, t`, the increment between the origin-centered
circle averages at radii `exp s` and `exp t` is sub-Gaussian with the exact
variance proxy `|s - t|`. For a nonnegative threshold `a`, the probability of
absolute increment at least `a` is bounded by
`2 exp (-a² / (2 |s - t|))`. The statement includes `s = t`: Lean defines
real division by zero to be zero, giving the valid (though non-sharp) bound 2.
For arbitrary thresholds the bound replaces `a` by `max a 0`; strict and
non-strict threshold events are measurable and satisfy the same bound. At
equal radii, a strict event with nonnegative threshold has probability zero.

The corrected paper defines the centered whole-plane GFF and its normalized
covariance in `paper/lqg_harmonic_ball-corrected.tex:359–368`. The existing
concentric covariance and joint-Gaussian arguments provide the centered
increment law for all log radii, including increments across the unit circle.
The proof uses that existing law from `CircleAverageLogRadiusFourthMoment`;
it does not use the fourth-moment identity. It follows the Gaussian-MGF and
union-bound route of `CircleAverageGaussianTail`, using Mathlib's optimized
sub-Gaussian Chernoff estimate to retain the exact variance. The existing
fixed-circle tail theorem has existential constants and does not itself imply
the required exact increment bound.

No new premise, Brownian identification, or simultaneous continuity assertion
is introduced. The import closure contains code by Leonardo Bonanno via
LatticeProb. All eight declarations print only `propext`, `Classical.choice`,
and `Quot.sound` as axioms; the proof file contains no forbidden placeholders.

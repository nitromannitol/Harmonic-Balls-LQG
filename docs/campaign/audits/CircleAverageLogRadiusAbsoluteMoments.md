# Absolute moments of log-radius circle-average increments

Task: `circle-average-log-radius-absolute-moments`.

For every real `p > 0` and every pair of real log radii `s, t`, the absolute
increment to the power `p` is integrable and its integral equals
`|s - t| ^ (p / 2)` times the standard Gaussian absolute `p`-moment. This
covers both signs of the log radii, including pairs crossing the unit circle,
and gives zero at equal log radii. The standard Gaussian moment is integrable.

The corrected paper specifies the whole-plane GFF normalization at
`paper/lqg_harmonic_ball-corrected.tex:384-388`. The proof uses the existing
exact centered Gaussian increment law and its variance `|s - t|` from
`CircleAverageLogRadiusFourthMoment.lean:30`. Mathlib's Gaussian `MemLp`
theorem gives integrability. The change of variables scales a standard real
Gaussian by the square root of its variance; the map identity also holds at
zero variance. No Brownian identification, continuity of a version, or new
literature input is assumed. The import closure contains code by Leonardo
Bonanno via LatticeProb.

All six declarations print only `propext`, `Classical.choice`, and
`Quot.sound` as axioms; the proof file has no forbidden placeholders.

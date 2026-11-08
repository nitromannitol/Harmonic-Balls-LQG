# Log-radius circle-average fourth moment

Task: `circle-average-log-radius-fourth-moment`.

For every pair of real `s, t`, the increment between the origin-centered circle
averages at radii `exp s` and `exp t` is centered Gaussian, with variance
`|s - t|`. Its fourth power is integrable and has expectation `3 |s - t|²`;
the same identity gives the uniform bound for the fourth absolute moment.
The statements include `s = t`, where the increment is identically zero.

The field and normalization are those of `Defs/GFF.lean`, corresponding to
the covariance and unit-circle normalization in the corrected paper,
lines 359–368. The pre-existing concentric covariance calculation proves the
increment variance for arbitrary positive radii: at the origin, the covariance
on either side of the unit circle is the minimum of the two distances from
zero in log radius, and it is zero across opposite sides. Thus increments
crossing the unit circle also have variance `|s - t|`. The proof uses the
joint Gaussian law of the two circles, not independence or an asserted
Brownian identification.

The exact fourth-moment identity, including the degenerate Gaussian, is
reused from Leonardo Bonanno's formalization in the pinned Lattice-Probability
package. The result makes no assertion about continuity of representatives,
and adds no external or proposed assumptions.

All six public declarations print only `propext`, `Classical.choice`, and
`Quot.sound` as axioms; the source contains no forbidden proof placeholders.

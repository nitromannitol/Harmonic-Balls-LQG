# Deterministic properness from annulus crossings

Task: `metric-properness-from-annulus-crossings`.

The crossing functional is the infimum of the existing `internalMetric` over
pairs of points on the inner and outer Euclidean spheres, with paths confined
to the closed annulus. The metric may be infinite if no such path exists.
The finite path estimate applies to any finite ordered family of bands, even if
the path backtracks, and does not assume geodesics or compactness.

For a continuous radial profile, the proof chooses the first outer-boundary
time and the last inner-boundary time before it. The intermediate value theorem
ensures the intervening segment stays in the closed band. First outer-boundary
times put the crossing segments for successive bands in order. Their lengths
sum to at most the original path length; the length-metric infimum gives the
finite distance bound.

The final theorem takes nonnegative inner radii, ordered bands, a sequence of
nonnegative extended-real lower bounds on their crossing lengths, and divergence
of the finite partial sums expressed as exceeding `ENNReal.ofReal C` for every
real `C`. It proves every set bounded with respect to `D` is Euclidean bounded.
In particular the framework permits radii `7 ^ n`; no LQG crossing estimates,
probabilistic laws, completeness, or bounded-compactness premise is asserted.

The statements are deterministic helper results, not numbered paper results
or literature inputs. No frozen draft declarations or external inputs changed.
Leonardo Bonanno is acknowledged in the Lean module.

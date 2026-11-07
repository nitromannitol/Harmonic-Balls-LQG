# Graph distance finiteness audit

`HarmonicBalls/Proofs/Sec2/GraphDistanceFiniteness.lean` proves that, for a
locally finite measure on ℂ with null singletons and every positive ε, the
Liouville graph distance between any two points is finite.

The proof uses regularity of locally finite measures on ℂ to choose a
positive-radius ball of mass below ε around each point. Compactness of the
range of `Path.segment` yields a finite subcover; `Finset.equivFin` enumerates
it to construct an `IsLiouvilleGraphCover`. The distance bound then follows
from `liouvilleGraphDistance_le`.

No full-support assumption, LQG existence claim, dimension identification,
or literature premise is used. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

We acknowledge Leonardo Bonanno's contributions to this formalization.

# Liouville graph-distance finiteness audit

Leonardo Bonanno contributed the compact-cover argument.

`HarmonicBalls/Proofs/Sec2/GraphDistanceFinite.lean` proves that for a locally
finite measure on `ℂ` with every singleton null and every `ε > 0`, there is a
finite admissible ball cover of the straight path between any two endpoints.
The existing `liouvilleGraphDistance_le` then gives distance different from
`⊤`. The conclusions use the unchanged definition and no literature premise.

The small-ball step applies Mathlib's compact-set outer approximation to a
singleton, then takes an open metric ball inside that neighborhood. Compactness
of the range of `Path.segment` supplies a finite subcover, reindexed by `Fin`.

The three declarations print only `propext`, `Classical.choice`, and
`Quot.sound` as axioms. The Lean source contains no `sorry`, `axiom`, `admit`,
`native_decide`, or heartbeat override. The lock-free check and module build
pass.

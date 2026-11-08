# Liouville graph distance: concatenation and symmetry

`IsLiouvilleGraphCover.trans` concatenates the two paths and ball families, preserving the original mass bounds. `IsLiouvilleGraphCover.symm` reverses a path with its ball family unchanged. Both use the actual cover definition, for arbitrary measures and real thresholds.

`exists_isLiouvilleGraphCover_of_ne_top` proves that the infimum is attained when finite. `liouvilleGraphDistance_triangle` treats either infinite summand explicitly, then combines covers realizing the two finite distances. `liouvilleGraphDistance_symm` identifies the sets in the defining infima, including the infinite case. No zero-diagonal claim is made: a constant path still needs a nonempty cover.

These deterministic helpers introduce no literature premise and do not close a numbered result. The module acknowledges Leonardo Bonanno's contributions. All five declarations print only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

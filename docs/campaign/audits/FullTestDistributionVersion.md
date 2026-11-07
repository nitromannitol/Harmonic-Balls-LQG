# Full-test distribution-valued version

Task: `gff-full-test-distribution-version`.

The reconstruction is Leonardo Bonanno's `pairJInv ⊤` applied to the raw
pairings at the countable tests `comb ⊤ c`. Its measurability follows from
`measurable_pairJInv`; `pairJInv_pairJ` identifies the reconstruction of any
distribution's pairings with that distribution.

For each fixed test, the equality event is measurable in the admissible
observation process. Equality of that process's law transfers the event from
Bonanno's normalized distribution-valued GFF, whose project realization has
exactly the same test pairings, to the given GFF. The exceptional set can
depend on the test. Countable intersection over `CoordJ` gives a common event
on which any fixed-test distribution-valued version equals the reconstruction;
thus any two versions are almost surely equal as distributions.

The extension uses the existing convention of zero on non-test functions.
`coordinateModification` proves the full project GFF specification for this
extension with the original circle-average process, without claiming equality
on non-tests. No additional literature hypothesis is used. The printed axioms
of the existence and uniqueness results are only `propext`,
`Classical.choice`, and `Quot.sound`.

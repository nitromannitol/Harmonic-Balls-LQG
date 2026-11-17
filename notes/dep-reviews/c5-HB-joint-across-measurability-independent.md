# Joint across measurability

The two exports in `PfefferCrossingJointMeasurable.lean` have been checked
at the stated types. The original across proof was introduced in commit
`68fd7bc1b1f9a2222446edadba621f490ed25c3e`; the later change in
`570d9ca3eef5dc8cc1780f3d9c551cfff12bea1e` adds a separate sphere selection
lemma and leaves those proofs unchanged. The current file SHA-256 is
`e61d343c8098bb419b47611613572aff0b6a939d4f4fdf7a112ebee4af670a1c`.

Pfeffer, arXiv:2104.04020v3, p. 5, defines across distance as the distance
between the annulus boundaries. `pfefferAcross` is the infimum over the two
circles for real-valued distances. This is the intended expression for a
Euclidean annulus and a real-valued metric. The printed weak-metric setting
also permits infinite distances; a source-level equivalence for that more
general carrier is not established by these exports. Outside the ordinary
annulus domain the Lean definition gives infinity if either radius is
negative, as independently checked for both radii.

The universal-measurability export has one argument, an extended-nonnegative
threshold; its other inputs are the continuous-map and product Borel types.
The random export takes an arbitrary measurable space, two s-finite measures,
a distance family, pointwise almost-everywhere measurability and an almost
sure Euclidean length metric. The last property expands to the diagonal,
separation, symmetry, triangle, Euclidean-topology and length fields in
`IsEuclideanLengthMetric`. These are assumptions of the auxiliary result;
the paper's definition of across distance is not itself this theorem.

The strict sublevel is the projection of the measurable relation containing
both circle equations and the strict distance inequality. The projection
result applies to standard Borel spaces and yields universal measurability,
which is pulled back under the measurable map using one continuous metric
representative. That representative equals the original family at all pairs
on one full-measure event. The product transfer uses the s-finite first
projection and does not require uncountably many separate null-set choices.
The parameter space is exactly `ℂ × (ℝ × ℝ)` with its product Borel structure.

Strict compilation, module build, exact typed applications, both negative
radius checks, and axiom checks passed. The two exports and the common
representative use only `propext`, `Classical.choice`, and `Quot.sound`.
The module build replayed two warnings in a dependency and no warnings in
this module. The generic consumer is checked; a separate application to the
full LQG metric assumptions hit the default elaboration limit and remains
unverified. No production caller of these exports was found. Source-level
carrier equivalence, comprehensive transitive semantic audit, full LQG
consumer and lead acceptance remain separate. This review makes no claim
about joint measurability of the around observable.

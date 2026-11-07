# Translated transposed changed-source obstruction

`HarmonicBalls/Proofs/Potential/TranslatedTransposedObstruction.lean` proves `no_transposed_changed_source_for_translated_observation` for any centre `z`, bounded open domain containing `ball z 2`, and arbitrary finite source measures. The first source gives the observation disc zero mass, and the correction is harmonic on the domain. The observation measure is `(volume + dirac z).restrict (ball z 2)`.

The proof restricts each source to the domain using the pointwise identity for literal transposed Green integrals, including totalized Bochner integrals. It maps the restricted sources and the observation measure by `x ↦ x - z`, transports harmonicity and the Green kernel, and applies the origin-centred obstruction. The first kernel argument is the source throughout; the diagonal and the atomic observation are retained. Radius two is essential to the invoked comparison. No general reciprocity is used, and this conditional obstruction does not prove the normal-kernel E51 statement or a numbered paper result.

The theorem prints only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

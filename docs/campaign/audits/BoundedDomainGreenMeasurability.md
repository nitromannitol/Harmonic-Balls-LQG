# Green-kernel joint measurability audit

- Task: `bounded-domain-green-joint-measurability` (analytic leaf only; no numbered-result closure).
- Declarations: `HarmonicBalls.measurable_greenFunction_uncurry` and
  `HarmonicBalls.measurable_greenFunction_uncurry_swap` in
  `HarmonicBalls/Proofs/Potential/BoundedDomainGreenMeasurability.lean`.
- Statement: jointly Borel measurable for every open `O : Set ℂ`, with no boundedness,
  Green-symmetry, or literature-input hypothesis. The stronger open-set conclusion
  includes the requested bounded-domain case. The coordinate-swapped conclusion is
  obtained by composition with `measurable_swap`, not by symmetry.
- Local identification: `exists_measurable_greenFunction_of_compact` applies
  Leonardo Bonanno's `greenHarmonicCorrectionBalayageStep_holds` to zero measure
  and zero mass, with a positive regularization radius provided by compactness.
  Its explicit pointwise agreement is used only for poles in the compact set and
  evaluation points in the open set. The Green definition supplies the diagonal and
  exterior zeros.
- Globalization: an open subset of the plane is locally compact and second countable,
  hence sigma-compact. Measurable representatives agree on intersections of compact
  pole patches and are glued using `exists_measurable_piecewise`; outside `O` the
  resulting kernel is zero.
- Verification: `lc` and `lb` pass. Forbidden-token scan of the Lean file is empty.
  Printed axioms for both final declarations: `propext`, `Classical.choice`,
  `Quot.sound` only.

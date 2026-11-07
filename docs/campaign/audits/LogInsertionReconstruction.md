# Logarithmic insertion reconstruction audit

The construction in `HarmonicBalls/Proofs/GFF/LogInsertionReconstruction.lean`
uses `Distribution.ofFun` for the actual locally integrable function
`x ↦ a * Real.log ‖x - z‖`, with arbitrary `z : ℂ` and `a : ℝ`.
Its evaluation theorem gives the Bochner integral against every full-plane
smooth compactly supported test. The separate integrability theorem uses the
existing translated-log result at `-z`, since `-z + x = x - z`.

Joint root/coefficient measurability follows from the cylinder measurable
structure and measurable test integrals. Leonardo Bonanno's countable
reconstruction gives a single almost-everywhere event on which the equality of
distributions holds for all roots and coefficients simultaneously. Raw
compatibility at a given test uses a second event depending on that test;
the resulting event still works for all roots and coefficients. Neither
statement asserts raw compatibility simultaneously for all tests.

No metric evaluation or metric law transfer is asserted. The module introduces
no literature premise. Its printed axioms are `propext`, `Classical.choice`,
and `Quot.sound` only; its source contains no forbidden proof escape.

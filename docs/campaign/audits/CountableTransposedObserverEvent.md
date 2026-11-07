# Countable transposed observer exceptional set

`exists_countable_transposed_observer_exceptional_set` is a deterministic
potential-theoretic helper, not a numbered-result closure. For a locally finite
observer with local positive-power upper growth, it treats a countable family of
bounded open domains and finite source measures carried almost everywhere in
the corresponding domains. The Green kernel has the literal argument order
`greenFunction (V n) y x`, with source `y` and observer `x`.

For each domain, mixed integrability gives integrability at almost every
restricted observer. Upper growth also gives zero source atom at almost every
observer. The restricted statements become global implications, and countable
intersection followed by a measurable null superset gives one global null set.
The source atom condition ensures the extended kernel's infinite diagonal does
not change its integral. Nonnegativity and Bochner integrability then identify
the finite extended integral with the real integral.

`ae_lqg_countable_transposed_observer_exceptional_set` selects the I2 field
event before quantifying over families; the observer null set depends on the
family and field sample. No new literature hypothesis or reciprocity is used.
The potential-theoretic infrastructure uses work of Leonardo Bonanno.
Lean's axiom print lists only `propext`, `Classical.choice`, and `Quot.sound`.

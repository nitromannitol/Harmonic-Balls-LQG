# Random logarithmic insertion: fixed-circle bridge

Task: `gff-random-log-insertion-fixed-circle`.

`HarmonicBalls/Proofs/GFF/RandomLogInsertionCircleBridge.lean` proves the
mollifier limit and Bonanno circle-average identity on a single almost-sure
fixed-circle event, with root and coefficient quantified after the event.
The proof combines the reconstructed GFF's fixed-circle mollifier convergence
and raw-circle identification with the deterministic insertion limit. It also
gives unit-circle and unit-centered identities and substitutes arbitrary,
potentially dependent random roots and coefficients pointwise. No joint
measurability of raw circle averages or common event across circles is claimed.

The inserted distribution, its fixed circle average, and the explicit fixed
and centered circle expressions are measurable for measurable parameters.
Leonardo Bonanno's distribution and circle-mollifier constructions are credited
in the consuming module. No new literature assumptions are introduced.

Validation: lock-free check `logs/lc/233554-1599263.log` and module build
`logs/lb/233611-1599855.log` passed. All ten printed axiom dependencies are
`propext`, `Classical.choice`, and `Quot.sound`. The Lean source has no `sorry`,
`axiom`, `admit`, `native_decide`, or heartbeat override. This is a helper
bridge and does not assert closure of any numbered paper result.

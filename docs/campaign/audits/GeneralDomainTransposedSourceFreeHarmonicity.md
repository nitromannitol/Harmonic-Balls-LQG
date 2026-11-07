# General-domain transposed source-free harmonicity

For a bounded open planar set `V` and a finite measure concentrated on a compact
`K ⊆ V`, the literal integral `x ↦ ∫ y, greenFunction V y x ∂ν` is harmonic
and continuous on `V \ K`. It is also harmonic and continuous on any open
`U ⊆ V` with `ν U = 0`. The restricted-measure versions require only finite
mass on `K`.

The proof uses right-variable harmonicity, joint measurability, and the existing
uniform bound on disjoint compact subsets of a bounded domain. Dominated
convergence gives continuity; the circle-bound harmonic integration theorem
then gives harmonicity. The source-free-open result replaces `K` by `K \ U`.
No Green reciprocity is assumed and no identification with `greenPotential`
is made. This is an analytic leaf, not a closure claim for a numbered result.
The potential-theoretic infrastructure is due to Leonardo Bonanno.

The file prints axioms for each result; all are standard (`propext`,
`Classical.choice`, and `Quot.sound`).

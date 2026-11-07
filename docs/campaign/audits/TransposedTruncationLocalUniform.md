# Transposed source truncation: local uniform convergence

`transposed_green_source_truncation_local_uniform` is a conditional analytic helper,
not a closure claim for a numbered result. The Green kernel retains source first,
observer second, including its prescribed diagonal. The finite measure is carried
by the bounded open domain, vanishes on the open observer set, and is carried by
the union of increasing measurable truncation sets. No compact source is assumed.

The complements decrease to a null set, so continuity from above and continuity of
`ENNReal.toReal` at zero give vanishing residual real mass. The existing source-free
mass bound yields uniform convergence of residual potentials on the compact set.
Pointwise source-slice integrability on the observer set justifies splitting the
Bochner integral over each truncation and its complement. The existing finite-source
harmonicity theorem gives harmonicity of both truncated and full potentials.

Lean's axiom print lists only `propext`, `Classical.choice`, and `Quot.sound`.
The potential-theoretic infrastructure uses work of Leonardo Bonanno.

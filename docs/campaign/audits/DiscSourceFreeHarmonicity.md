# Disc source-free potential harmonicity

The analytic leaf `HarmonicBalls.Proofs.Potential.DiscSourceFreeHarmonicity`
proves harmonicity and continuity of `greenPotential (ball 0 R) ν` off a
compact concentration set `K`, assuming `IsFiniteMeasure ν`, `IsCompact K`,
`K ⊆ ball 0 R`, and `ν Kᶜ = 0`. It also proves both properties on any open
`U ⊆ ball 0 R` satisfying `ν U = 0`, using the compact concentration set
`K \ U`. The conclusions use the actual totalized `greenPotential`; the
kernel is integrable at every relevant point by
`integrable_greenFunction_of_compact_source` and
`integrable_greenFunction_of_source_free_open` in
`Proofs/Potential/GeneralDomainSourceFreePotential.lean`. No positivity of R is
needed: the compact-source statement is vacuous off an empty disc, and the
open-source statement forces U empty if the disc is empty.

Continuity follows from dominated convergence on a closed disc separated from
K, using `Section6.exists_uniform_bound_greenFunction`. Harmonicity follows
from `Section6.harmonicOnNhd_restricted_greenPotential_of_kernel`, disc Green
symmetry, and uniform bounds on circles. The proof uses the potential-theory
infrastructure of Leonardo Bonanno. No Hölder, volume-growth, reciprocity, or
new literature hypothesis occurs. This is an analytic leaf, not a numbered
result closure; general-domain harmonicity and full representatives remain open.

The file prints axioms for all six declarations; each uses only `propext`,
`Classical.choice`, and `Quot.sound`. The lock-free compile check and shared module build passed.

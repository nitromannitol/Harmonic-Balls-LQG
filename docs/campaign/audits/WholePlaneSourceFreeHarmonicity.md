# Whole-plane source-free harmonicity

For a finite measure concentrated on a compact set `K`,
`harmonicOnNhd_greenPotential_univ_of_compact_source` proves that its literal
whole-plane Green potential is harmonic on `Kᶜ`; the corresponding
continuity theorem follows. The two source-free-open theorems give the same
conclusions on any open set of zero source mass, using the compact
concentration set `K \ U`.

The proof encloses the source and observer in a disc and uses the pointwise
disc correction identity locally off `K`. The whole-plane kernel is
integrable there by continuity and compact boundedness of the logarithmic
kernel; the disc kernel uses the existing unconditional compact-source
integrability theorem. The disc potential and correction are harmonic. No
distributional identity, reciprocity assumption, or additional literature
input is used. Literal kernel order and totalized integral semantics are
preserved.

All four declarations compile and depend only on `propext`,
`Classical.choice`, and `Quot.sound`. This analytic result does not close a
numbered result. The potential-theoretic infrastructure uses work of Leonardo
Bonanno.

# Finite-source disc representatives

`ae_finiteSource_disc_representative` treats an explicit locally finite observation
measure with positive-power local upper growth. Each source is finite and
concentrated on a compact subset of the disc. Its conclusion gives a single
full-measure set where both whole-plane and disc kernels are Bochner integrable
for each source, neither source charges the observer, and the stated signed
representative identity holds. The correction `q - correction₁ + correction₂`
is harmonic on the disc. The signs follow from the two identities
`whole = disc + correction`.

`ae_lqg_finiteSource_disc_representative` takes I2 as an explicit hypothesis,
along with the stated GFF and LQG-measure hypotheses. Its outer probability-one
event is simultaneous in the disc, sources, and harmonic function; the inner
exceptional set of observers may depend on those choices. The proof uses the
same I2 exponent range and local finiteness as
`ae_lqg_greenPotential_exceptional_set`.

These are almost-everywhere representative statements, not pointwise bounded
test-class membership, a Laplacian assertion, or closure of E51 or any numbered
result. No general-domain reciprocity is used. Both declarations print only
`propext`, `Classical.choice`, and `Quot.sound`. The underlying potential theory
uses work of Leonardo Bonanno.

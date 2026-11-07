# Translated finite-source disc correction

`translatedDiscSourceCorrection` composes the centred correction with the
translation of both the finite source and the observer by minus the centre.
`harmonicOnNhd_translatedDiscSourceCorrection` proves harmonicity on the disc
for a finite source concentrated on a compact subset of that disc.

`greenPotential_univ_eq_translatedDisc_add_correction` proves the pointwise
whole-plane/disc identity for an interior observer not charged by the source,
assuming both kernels are Bochner integrable and the source is almost surely
in the disc. No compact concentration or finite-measure assumption is needed
for this pointwise identity.

`ae_greenPotential_univ_eq_translatedDisc_add_correction` supplies both
integrability assertions and the uncharged condition for planar-almost every
interior observer of a finite source almost surely in the disc. The proof
transports the centred theorem using the measurable translation equivalence and
translation invariance of planar volume; it preserves totalized integral and
diagonal semantics.

These are analytic leaves, not closure of a numbered result, nor a claim of
pointwise bounded test-class membership or a Laplacian assertion. The
potential-theoretic infrastructure uses work of Leonardo Bonanno.

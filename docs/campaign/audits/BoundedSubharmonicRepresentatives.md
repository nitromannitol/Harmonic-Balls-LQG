# Bounded subharmonic representatives: localization and an atomic obstruction

Status: the full `HasBoundedSubharmonicRepresentatives` assertion is **not proved or refuted**. The new Lean file proves the bounded-open localization and a conditional representative construction for two separately corrected sources. It preserves both measures, their compact concentration, the positive-source sign condition, and the negative-source non-atom condition; it requires the new negative-kernel integrability and the two correction identities at the pole and almost everywhere. These hypotheses are not asserted as literature inputs.

## A concrete obstruction to retaining the source

Take `O = ball 0 2`, `V = ball 0 1`, and `ν₂ = dirac 0`. For `0 < ‖x‖ < 1`, the explicit disc formula `greenFunction_ball` and symmetry `greenFunction_ball_comm` give

`greenPotential O ν₂ x - greenPotential V ν₂ x = (2 * π)⁻¹ * log 2 > 0`.

At `x = 0`, both potentials are zero by the frozen diagonal convention; the Lean theorem `dirac_source_correction_at_atom` proves that any exact correction there must be zero. Consequently no function harmonic on `V` can equal that difference both at `0` and almost everywhere on a disc around `0` for `μ = volume + dirac 0`: continuity makes its value at `0` equal the positive constant. The Lean theorem `no_dirac_harmonic_correction_on_discs` checks the disc calculation and the contradiction, including the almost-everywhere statement for `volume + dirac 0`. Its kernel calculation is `greenPotential_dirac_zero_ball`.

This example occurs within the intended carrier: take `Λ = ball 0 (1/2)`, `z = 1/4`, positive source zero, negative source `dirac 0`, and `q = 0`. The Lean theorem `neg_dirac_disc_mem_subharmonicBallTestClass` verifies this membership, including that the negative source does not charge `z` and that its old kernel is integrable there. Thus a source-by-source correction with unchanged measure cannot be assumed for arbitrary observation measures. This does **not** refute a representative with different source measures, a different bounded domain, or a correction of the signed difference as a whole. Indeed, this example already has a bounded original witness `O`, so the original test itself is a bounded representative.

The obstruction also holds for a genuinely unbounded original witness: `no_dirac_harmonic_correction_univ_to_ball` proves that for `O = univ`, the same source and `μ = volume + dirac 0` restricted to any positive-radius observation disc `ball 0 ρ`, and every concentric disc `V = ball 0 R` with `ρ ≤ R` and `R ≠ 1`, there is no harmonic correction on `V` giving the required almost-everywhere equality. The proof uses the checked whole-plane kernel and the explicit disc formula. This is a precise obstruction to this particular source-preserving localization, not to the target property: radius one does supply a representative in this example.

For the larger observation set `Λ = ball 0 2`, the new theorem `no_concentric_disc_source_correction_for_large_observation` applies the actual closure-containment requirement and rules out **every** concentric disc as a source-preserving harmonic localization. The frozen test itself is admissible, for example at pole `z = 1`, by `neg_univ_dirac_zero_mem_subharmonicBallTestClass`. This theorem alone does not exclude nonconcentric domains or changed source measures and does not prove failure of bounded representatives.

The stronger theorem `no_bounded_domain_continuousAt_source_correction_for_large_observation` rules out unchanged-source localization to **every bounded domain** containing `ball 0 R`, for any `R > 1`, even if the correction is only assumed continuous at the atom and observations are limited to `ball 0 ρ` for any `0 < ρ ≤ R`. Domain monotonicity bounds the new Green potential below by the radius-two disc potential almost everywhere nearby, forcing the correction below a strictly negative constant there; the observed atom forces its value at the atom to be zero. `no_bounded_domain_pointwise_source_correction_for_large_observation` records the obstruction for pointwise equality, connecting it to the universal-measure reduction below. Changing the source measures remains a possible route, so this still does not refute the target.

`no_changed_source_continuous_residual_for_large_observation` extends the
large-disc obstruction to changed sources: the bounded-domain positive
source can be arbitrary and its negative source can be `dirac 0 + η₂`.
The result explicitly assumes continuity at the atom of the harmonic term
and both residual potentials, and integrability of the negative residual
kernel almost everywhere for `volume + dirac 0` on the observation disc.
Under those conditions, no matching representative exists. It does not show
that arbitrary candidate sources have this decomposition or satisfy these
regularity and integrability conditions, and is not a full counterexample.

The representative property is downward closed under absolute continuity of restricted observation measures: `hasBoundedSubharmonicRepresentatives_of_absolutelyContinuous` transfers an existing representative result to any dominated measure. This reduction does not establish the property for the dominating measure.

## Universal measures require pointwise representatives

`forall_hasBoundedSubharmonicRepresentatives_iff_pointwise` proves that, for measurable Λ, the property for **every** observation measure is equivalent to choosing, for each frozen test, one bounded-witness test agreeing at the pole and at every point of Λ. The forward direction uses counting measure on ℂ, which is permitted by the unrestricted Lean quantifier and forces pointwise equality; the reverse direction works for every measure. Counting measure is not locally finite on a nonempty open set, so this equivalence concerns the unrestricted audit obligation and does not by itself settle a version limited to LQG measures. It neither proves nor disproves the pointwise representative assertion.

## Finitely supported observation measures

`hasBoundedSubharmonicRepresentatives_of_ae_mem_finset` proves the exact representative property for **every** frozen test whenever Λ is bounded and the restricted observation measure is concentrated almost everywhere on a finite set. It uses the real part of a complex Lagrange interpolation polynomial through the observation points and the pole. This proof does not assume anything about the test's original domain or sources. In particular, `hasBoundedSubharmonicRepresentatives_dirac` covers a Dirac observation measure at any point, whether or not it equals the pole. These cases do not resolve general observation measures.

## A checked whole-plane representative

The file now proves `not_isHarmonicMinorant_univ_newtonKernel`, using the existing circle-average bound on every disc, and derives `greenFunction_univ_eq_newtonKernel` from the actual frozen definition. No non-Greenian behavior is assumed. `neg_univ_dirac_zero_mem_subharmonicBallTestClass` verifies that the corresponding negative Dirac potential is in the full class when the pole differs from the atom.

`greenPotential_univ_dirac_zero_eq_unitDisc` proves equality with the unit-disc potential throughout that disc, including at the atom. Hence `univ_dirac_zero_has_bounded_representative` constructs a bounded representative for this one whole-plane test for every observation measure, assuming `closure Λ ⊆ ball 0 1`, `z ∈ Λ`, and `z ≠ 0`. The matching works because the disc's harmonic correction for this centered source vanishes identically; it does not establish the analogous claim for general source measures or other domains.

## A changed-source representative away from the atom

`neg_univ_dirac_mem_bounded_of_source_outside_closure` handles a whole-plane negative Dirac potential at any atom outside the closure of a bounded observation set. The function is harmonic on the complement of the atom, so the bounded witness uses this same function as its harmonic part and both source measures equal zero. Equality holds everywhere, including at the pole, and the sign, support, non-atom and integrability conditions are automatic. This provides a changed-source construction for this restricted case; it does not address an atom in the observation-set closure or general source measures.

`univ_two_dirac_mem_subharmonicBallTestClass` checks the full frozen class for the difference of a positive whole-plane Dirac potential at `a` and a negative one at zero, when `a ∉ Λ` and `z ≠ 0`. `univ_two_dirac_has_bounded_representative` constructs a bounded witness for every observation measure when `closure Λ ⊆ ball 0 1`, `z ∈ Λ`, `z ≠ 0`, and `a ∉ ball 0 1`. It eliminates the positive source and absorbs its potential into the harmonic part; it keeps the negative source at zero in the unit disc, where the two kernels agree even at the atom. The two-source test itself is thus admissible and the construction handles observations at the negative atom. General sources and larger observation sets remain open.

`univ_two_dirac_has_bounded_representative_of_zero_diagonal_correction` extends this construction to a negative atom `a` in `ball 0 R` whenever `‖R² - conj a * a‖ = R`. The explicit disc harmonic minorant then vanishes at `a`, so the frozen diagonal value agrees as well as all off-diagonal values; a positive atom outside the disc is absorbed into the harmonic part. `univ_dirac_sub_dirac_mem_subharmonicBallTestClass` checks membership of the original two-source test. The condition is nonempty beyond the centered unit disc: `radius_two_sqrt_two_diagonal_correction` and `univ_two_dirac_sqrt_two_has_bounded_representative` prove the case `R = 2`, `a = √2`. These results allow arbitrary observation measures, including atoms, but do not settle general source measures or the candidate negative atom at zero in a larger disc.

The complementary result `univ_two_dirac_has_bounded_representative_of_measure_atom_eq_zero` removes the zero-diagonal-correction condition if `(μ.restrict Λ) {a} = 0`: the pole is distinct from the negative atom, and the potential correction is applied there and almost everywhere on the observation set. The positive atom is again outside the bounded witness disc and is eliminated. `univ_two_dirac_has_bounded_representative_of_ac_volume` specializes to observation measures absolutely continuous with respect to area. These are proved special cases, not an assumed polar-nullness principle, and they do not handle an observation measure charging the negative atom when its diagonal correction is nonzero.

`univ_three_dirac_has_bounded_representative_of_measure_atoms_eq_zero` extends the changed-source construction to a positive point source outside the witness disc and two negative point sources inside it. It retains both negative sources, absorbs the positive source and the two disc corrections into the harmonic part, and matches the original function at the pole and almost everywhere when the restricted observation measure gives each negative atom zero mass. `univ_dirac_sub_two_dirac_mem_subharmonicBallTestClass` also checks that the original potential belongs to the full frozen class, including its source support and pole conditions. `univ_three_dirac_has_bounded_representative_of_ac_volume` specializes the construction to observation measures absolutely continuous with respect to planar area. The two negative atoms may coincide. This remains a special case and does not settle observations charging either atom or arbitrary source measures.

`neg_univ_finset_sum_dirac_mem_subharmonicBallTestClass` verifies the full frozen test for a whole-plane negative potential of any finite set of unit point masses when the pole avoids that set. `neg_univ_finset_sum_dirac_has_bounded_representative` constructs a bounded disc witness when the source set is inside the disc and the restricted observation measure assigns that finite set zero mass. It uses an explicit finite sum of harmonic corrections and checks the pole and support conditions. This covers arbitrarily many negative atoms, but not arbitrary weights or general source measures, and does not handle observation measures charging the sources.

`univ_dirac_sub_finset_sum_dirac_mem_subharmonicBallTestClass` and `univ_dirac_sub_finset_sum_dirac_has_bounded_representative` add one positive whole-plane point source outside the witness disc to the finite-negative-source construction. The positive potential is absorbed into the harmonic correction, so the bounded witness removes that source; the negative source set must still be uncharged by the restricted observation measure. The original function is checked against the full frozen source, support, and pole conditions. General source measures and observation measures charging negative atoms remain unresolved.

`univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_diagonal` handles observation measures that may charge some negative source atoms: only the finite subset at which the disc harmonic correction has nonzero diagonal value must be null. At all other source atoms, the whole-plane and corrected disc kernels agree even with the frozen diagonal convention. `univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_zero_diagonal` permits an arbitrary observation measure when all the diagonal corrections vanish. These conclusions remain restricted to finite unit point sources and the stated disc geometry; they do not resolve arbitrary source measures or charged atoms with nonzero diagonal corrections.

`univ_finset_sum_dirac_sub_finset_sum_dirac_mem_subharmonicBallTestClass` verifies the full test-class membership of a whole-plane potential with finite positive and negative unit point sources, when the positive atoms avoid Λ and the negative atoms avoid the pole. `univ_finset_sum_dirac_sub_finset_sum_dirac_has_bounded_representative` treats finite sets of positive atoms outside the containing disc by absorbing their potentials into the harmonic part, while retaining the finite negative-source construction and its exact condition on observed atoms with nonzero diagonal correction. General source measures and the unresolved charged-atom cases remain open.

## Nonnegative scaling of tests and representatives

`subharmonicBallTestClass_smul` and `boundedSubharmonicBallTestClass_smul` prove closure under nonnegative real scaling, including the source support and pole conditions. `boundedSubharmonicRepresentative_smul` transports pole equality and almost-everywhere equality. Applied to the finite-source changed-source construction, `univ_smul_dirac_sub_finset_sum_dirac_has_bounded_representative` permits any common nonnegative mass under the same diagonal and observation-measure conditions. It does not cover independently weighted or general source measures, nor does it settle the full representative property.

## Outstanding proof obligation

For a non-atomic example beyond finite point sources,
`neg_univ_circleDensity_mem_subharmonicBallTestClass` verifies that a smooth
normalized annular density gives an admissible whole-plane negative-source test;
`circleDensity_source_isProbabilityMeasure` checks that this source is nonzero,
and its absolute continuity with respect to area gives non-atomicity. When the
pole and measurable bounded observation set lie inside the annulus's inner
disc, `univ_circleDensity_has_bounded_representative` removes the entire source
and uses the constant harmonic representative, for an arbitrary observation
measure. The shell identity is pointwise, including every observed atom. This
is a special geometry, not a construction for general sources or domains.

`univ_circleDensity_add_dirac_has_bounded_representative` combines the annular
source with a negative Dirac source at the centre of the unit disc. The new
representative removes the annular source but retains the Dirac source, and
works for arbitrary observation measures, including those charging the atom.
`neg_univ_circleDensity_add_dirac_mem_subharmonicBallTestClass` checks the
mixed source against the complete frozen carrier. More generally,
`univ_add_circleDensity_has_bounded_representative` transports an existing
representative for an arbitrary negative measure after adding an annular
source, subject to explicit integrability of the original kernel at the pole
and almost everywhere on the observation set. It does not provide the original
representative or handle its nonintegrability points.

`greenPotential_add_integrable_source` records the exact totalized-integral
case split for adding an integrable source: the sum has the usual potential
when the original kernel is integrable, and is zero otherwise. Consequently,
`greenPotential_add_zero_source` and
`neg_greenPotential_add_zero_source_has_bounded_representative` allow a
zero-potential source to be added while retaining an existing bounded
representative, without assuming the original kernel is integrable at the
pole or at observed points. The latter result explicitly requires the added
source to be integrable and have zero potential at the pole and almost
everywhere on the observation set; it neither constructs that source nor
establishes the original representative.

`bounded_representative_of_changed_sources` gives a general transport step for arbitrary
old and replacement measures, without requiring the two source corrections separately.
The remaining construction must choose a bounded open `V ⊆ O`, compact `K ⊆ V`,
finite replacement measures `η₁, η₂` concentrated on `K`, and a function harmonic
on `V`, with `η₁ Λ = 0`, `η₂ {z} = 0`, and `Integrable (greenFunction V z) η₂`.
It must establish equality of the old signed potential and the replacement signed
potential plus the harmonic function at `z` and `μ.restrict Λ`-almost everywhere.
These are explicit hypotheses of the transport lemma, not established facts or
literature inputs; in particular the source-preserving counterexamples do not rule
out this changed-source construction.

The exact target remains

```lean
∀ (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ),
  Bornology.IsBounded Λ → IsOpen Λ → z ∈ Λ →
  HasBoundedSubharmonicRepresentatives μ Λ z
```

Its validity is unresolved. A proof must handle arbitrary open `O`, including non-Greenian and disconnected cases, the separate Bochner junk values at nonintegrability points, atoms observed by `μ`, and preservation of negative-source pole integrability. The paper's Riesz-decomposition reference (corrected TeX lines 761–765) concerns the classical potential-theoretic functions and does not by itself supply this frozen real-valued, arbitrary-μ assertion. No polar-nullness or representative assertion has been added as an assumption or staged as a literature input.

The Lean file imports the existing test-class audit and `Proofs/Potential/GreenBall` `Proofs/Potential/GreenPositivity`, and Mathlib Lagrange interpolation and polynomial analyticity. Its printed axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The disc obstruction uses `Proofs/Potential/GreenBall.lean:278,296` and is formally proved in the new Lean file. Leonardo Bonanno is credited in the consuming Lean file.

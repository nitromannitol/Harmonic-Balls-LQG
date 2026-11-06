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

`univ_three_dirac_has_bounded_representative_of_measure_atoms_eq_zero` extends the changed-source construction to a positive point source outside the witness disc and two negative point sources inside it. It retains both negative sources, absorbs the positive source and the two disc corrections into the harmonic part, and matches the original function at the pole and almost everywhere when the restricted observation measure gives each negative atom zero mass. The two negative atoms may coincide. This remains a special case and does not settle observations charging either atom or arbitrary source measures.

## Outstanding proof obligation

The exact target remains

```lean
∀ (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ),
  Bornology.IsBounded Λ → IsOpen Λ → z ∈ Λ →
  HasBoundedSubharmonicRepresentatives μ Λ z
```

Its validity is unresolved. A proof must handle arbitrary open `O`, including non-Greenian and disconnected cases, the separate Bochner junk values at nonintegrability points, atoms observed by `μ`, and preservation of negative-source pole integrability. The paper's Riesz-decomposition reference (corrected TeX lines 761–765) concerns the classical potential-theoretic functions and does not by itself supply this frozen real-valued, arbitrary-μ assertion. No polar-nullness or representative assertion has been added as an assumption or staged as a literature input.

The Lean file imports the existing test-class audit and `Proofs/Potential/GreenBall` `Proofs/Potential/GreenPositivity`, and Mathlib Lagrange interpolation and polynomial analyticity. Its printed axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The disc obstruction uses `Proofs/Potential/GreenBall.lean:278,296` and is formally proved in the new Lean file. Leonardo Bonanno is credited in the consuming Lean file.

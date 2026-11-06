# Bounded subharmonic representatives: localization and an atomic obstruction

Status: the full `HasBoundedSubharmonicRepresentatives` assertion is **not proved or refuted**. The new Lean file proves the bounded-open localization and a conditional representative construction for two separately corrected sources. It preserves both measures, their compact concentration, the positive-source sign condition, and the negative-source non-atom condition; it requires the new negative-kernel integrability and the two correction identities at the pole and almost everywhere. These hypotheses are not asserted as literature inputs.

## A concrete obstruction to retaining the source

Take `O = ball 0 2`, `V = ball 0 1`, and `ν₂ = dirac 0`. For `0 < ‖x‖ < 1`, the explicit disc formula `greenFunction_ball` and symmetry `greenFunction_ball_comm` give

`greenPotential O ν₂ x - greenPotential V ν₂ x = (2 * π)⁻¹ * log 2 > 0`.

At `x = 0`, both potentials are zero by the frozen diagonal convention; the Lean theorem `dirac_source_correction_at_atom` proves that any exact correction there must be zero. Consequently no function harmonic on `V` can equal that difference both at `0` and almost everywhere on a disc around `0` for `μ = volume + dirac 0`: continuity makes its value at `0` equal the positive constant. The Lean theorem `no_dirac_harmonic_correction_on_discs` checks the disc calculation and the contradiction, including the almost-everywhere statement for `volume + dirac 0`. Its kernel calculation is `greenPotential_dirac_zero_ball`.

This example occurs within the intended carrier: take `Λ = ball 0 (1/2)`, `z = 1/4`, positive source zero, negative source `dirac 0`, and `q = 0`. The Lean theorem `neg_dirac_disc_mem_subharmonicBallTestClass` verifies this membership, including that the negative source does not charge `z` and that its old kernel is integrable there. Thus a source-by-source correction with unchanged measure cannot be assumed for arbitrary observation measures. This does **not** refute a representative with different source measures, a different bounded domain, or a correction of the signed difference as a whole. Indeed, this example already has a bounded original witness `O`, so the original test itself is a bounded representative.

The obstruction also holds for a genuinely unbounded original witness: `no_dirac_harmonic_correction_univ_to_ball` proves that for `O = univ`, the same source and observation measure, and every concentric disc `V = ball 0 R` with `R > 1/2` and `R ≠ 1`, there is no harmonic correction on `V` giving the required almost-everywhere equality. The proof uses the checked whole-plane kernel and the explicit disc formula. This is a precise obstruction to this particular source-preserving localization, not to the target property: radius one does supply a representative in this example.

The representative property is downward closed under absolute continuity of restricted observation measures: `hasBoundedSubharmonicRepresentatives_of_absolutelyContinuous` transfers an existing representative result to any dominated measure. This reduction does not establish the property for the dominating measure.

## Finitely supported observation measures

`hasBoundedSubharmonicRepresentatives_of_ae_mem_finset` proves the exact representative property for **every** frozen test whenever Λ is bounded and the restricted observation measure is concentrated almost everywhere on a finite set. It uses the real part of a complex Lagrange interpolation polynomial through the observation points and the pole. This proof does not assume anything about the test's original domain or sources. In particular, `hasBoundedSubharmonicRepresentatives_dirac` covers a Dirac observation measure at any point, whether or not it equals the pole. These cases do not resolve general observation measures.

## A checked whole-plane representative

The file now proves `not_isHarmonicMinorant_univ_newtonKernel`, using the existing circle-average bound on every disc, and derives `greenFunction_univ_eq_newtonKernel` from the actual frozen definition. No non-Greenian behavior is assumed. `neg_univ_dirac_zero_mem_subharmonicBallTestClass` verifies that the corresponding negative Dirac potential is in the full class when the pole differs from the atom.

`greenPotential_univ_dirac_zero_eq_unitDisc` proves equality with the unit-disc potential throughout that disc, including at the atom. Hence `univ_dirac_zero_has_bounded_representative` constructs a bounded representative for this one whole-plane test for every observation measure, assuming `closure Λ ⊆ ball 0 1`, `z ∈ Λ`, and `z ≠ 0`. The matching works because the disc's harmonic correction for this centered source vanishes identically; it does not establish the analogous claim for general source measures or other domains.

## Outstanding proof obligation

The exact target remains

```lean
∀ (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ),
  Bornology.IsBounded Λ → IsOpen Λ → z ∈ Λ →
  HasBoundedSubharmonicRepresentatives μ Λ z
```

Its validity is unresolved. A proof must handle arbitrary open `O`, including non-Greenian and disconnected cases, the separate Bochner junk values at nonintegrability points, atoms observed by `μ`, and preservation of negative-source pole integrability. The paper's Riesz-decomposition reference (corrected TeX lines 761–765) concerns the classical potential-theoretic functions and does not by itself supply this frozen real-valued, arbitrary-μ assertion. No polar-nullness or representative assertion has been added as an assumption or staged as a literature input.

The Lean file imports the existing test-class audit and `Proofs/Potential/GreenBall` `Proofs/Potential/GreenPositivity`, and Mathlib Lagrange interpolation and polynomial analyticity. Its printed axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The disc obstruction uses `Proofs/Potential/GreenBall.lean:278,296` and is formally proved in the new Lean file. Leonardo Bonanno is credited in the consuming Lean file.

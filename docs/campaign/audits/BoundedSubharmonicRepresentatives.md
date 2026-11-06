# Bounded subharmonic representatives: localization and an atomic obstruction

Status: the full `HasBoundedSubharmonicRepresentatives` assertion is **not proved or refuted**. The new Lean file proves the bounded-open localization and a conditional representative construction for two separately corrected sources. It preserves both measures, their compact concentration, the positive-source sign condition, and the negative-source non-atom condition; it requires the new negative-kernel integrability and the two correction identities at the pole and almost everywhere. These hypotheses are not asserted as literature inputs.

## A concrete obstruction to retaining the source

Take `O = ball 0 2`, `V = ball 0 1`, and `ν₂ = dirac 0`. For `0 < ‖x‖ < 1`, the explicit disc formula `greenFunction_ball` and symmetry `greenFunction_ball_comm` give

`greenPotential O ν₂ x - greenPotential V ν₂ x = (2 * π)⁻¹ * log 2 > 0`.

At `x = 0`, both potentials are zero by the frozen diagonal convention; the Lean theorem `dirac_source_correction_at_atom` proves that any exact correction there must be zero. Consequently no function harmonic on `V` can equal that difference both at `0` and almost everywhere on a disc around `0` for `μ = volume + dirac 0`: continuity makes its value at `0` equal the positive constant. The Lean theorem `no_dirac_harmonic_correction_on_discs` checks the disc calculation and the contradiction, including the almost-everywhere statement for `volume + dirac 0`. Its kernel calculation is `greenPotential_dirac_zero_ball`.

This example occurs within the intended carrier: take `Λ = ball 0 (1/2)`, `z = 1/4`, positive source zero, negative source `dirac 0`, and `q = 0`. The Lean theorem `neg_dirac_disc_mem_subharmonicBallTestClass` verifies this membership, including that the negative source does not charge `z` and that its old kernel is integrable there. Thus a source-by-source correction with unchanged measure cannot be assumed for arbitrary observation measures. This does **not** refute a representative with different source measures, a different bounded domain, or a correction of the signed difference as a whole. Indeed, this example already has a bounded original witness `O`, so the original test itself is a bounded representative.

## Outstanding proof obligation

The exact target remains

```lean
∀ (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ),
  Bornology.IsBounded Λ → IsOpen Λ → z ∈ Λ →
  HasBoundedSubharmonicRepresentatives μ Λ z
```

Its validity is unresolved. A proof must handle arbitrary open `O`, including non-Greenian and disconnected cases, the separate Bochner junk values at nonintegrability points, atoms observed by `μ`, and preservation of negative-source pole integrability. The paper's Riesz-decomposition reference (corrected TeX lines 761–765) concerns the classical potential-theoretic functions and does not by itself supply this frozen real-valued, arbitrary-μ assertion. No polar-nullness or representative assertion has been added as an assumption or staged as a literature input.

The Lean file imports the existing test-class audit and `Proofs/Potential/GreenBall`. Its printed axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The disc obstruction uses `Proofs/Potential/GreenBall.lean:278,296` and is formally proved in the new Lean file. Leonardo Bonanno is credited in the consuming Lean file.

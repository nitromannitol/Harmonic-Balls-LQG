# Fixed-pole diagonal criterion

`exists_continuousAt_fixedPole_correction_iff` in `HarmonicBalls/Proofs/Potential/FixedPoleDiagonalCriterion.lean` characterizes a correction continuous at `z` for bounded open `V` containing `z`. The observation measure is `(volume + dirac z).restrict V`, and the criterion is exactly `(greatestHarmonicMinorant V (newtonKernelEReal z) z).toReal = 0`.

The proof uses the established harmonicity of that actual greatest harmonic minorant on `V`, not a new input. Off the pole the identity follows from the Green definition; at the pole both Green functions have the frozen zero diagonal. The atom forces the proposed correction to vanish there. Volume equality away from the pole and continuity, using positive-volume balls, identify its value with that of the harmonic correction. Conversely, that correction supplies a pointwise identity throughout `V` when its pole value is zero. The Green potential retains the totalized Bochner integral and its original argument order.

The criterion depends on domain scale and normalization: the existing explicit disc minorant formula gives pole value `-(2π)⁻¹ log R` at the centre of `ball 0 R`, hence the value varies with `R`. This is a conditional criterion, not a verdict for general representatives or a numbered paper result.

The theorem prints only `propext`, `Classical.choice`, and `Quot.sound` as axioms. The potential-theoretic infrastructure uses work of Leonardo Bonanno.

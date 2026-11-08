# Metric Weyl exponent sign: partial formalization

The target `∀ γ ξ 𝔇, 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 → 0 < ξ` is not yet proved. No additional premise has been introduced. The whole-plane GFF existence used by the proposed route relies on Leonardo Bonanno's construction.

`HarmonicBalls/Proofs/GFF/MetricXiSign.lean` proves the fixed distance law for arbitrary whole-plane GFF realizations and for each normalized affine field, positivity of the fixed distance, the exact second moment of `Bₙ = hcirc (exp (-n)) 0`, the almost-sure and in-measure convergence of `Xₙ = 𝔇 (hC) 0 (exp (-n))` to zero, and the fixed-scale almost-sure identity `Xₙ = exp (ξ * (Bₙ - lqgQ γ * n)) * Yₙ`. The identity holds separately for each n; countable intersection is still needed when a simultaneous event is used. The law theorem uses the measurable observable decoder, not samplewise representatives.

Remaining implications, on the probability space supplied by `exists_projectWholePlaneGFF`, with `Yₙ = 𝔇 (affinePairing hC hcirc (exp (-n)) 0) 0 1`:

1. Prove `TendstoInMeasure P (fun n ω => hcirc ω (Real.exp (-(n : ℝ))) 0 / (n : ℝ)) atTop (fun _ => 0)` from the second moment and Chebyshev.
2. Prove `TendstoInMeasure P (fun n ω => Real.log (Yₙ ω) / (n : ℝ)) atTop (fun _ => 0)` from fixed-law tightness and positivity. No independence is required.
3. Combine the identity, positivity, and these limits to obtain the log-distance limit `-ξ * lqgQ γ` in probability, and use the existing zero limit to rule out `ξ < 0`. Separately, `ξ = 0` makes `Xₙ` identically distributed with the positive fixed distance and contradicts its zero limit. Establish `0 < lqgQ γ` from `0 < γ`.

These are unproved formalization steps, not identified missing literature inputs or a mathematical counterexample.

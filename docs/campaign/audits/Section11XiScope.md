# Section 11: the sign of the Weyl exponent

**Finding.** The metric axioms imply `0 < ξ` for `0 < γ` by the scaling
argument below. This is a mathematical argument, not yet a checked Lean
declaration. No counterexample has been established, and no change to the
frozen statements or additional literature premise is justified by this audit.
The argument is the one in the operator-approved
`~/paper-fleets/hb/notes/sec11-proof/sec11-proof.tex:103–114`; its audit
confirms that step. The corrected paper specifies `ξ = γ / dγ` and `dγ > 2`
at `paper/lqg_harmonic_ball-corrected.tex:426,443–446`, but that formula is
not a field of the Lean metric structure.

## Argument for the exact interface

Choose the actual probability-space GFF given by
`exists_projectWholePlaneGFF` (`Proofs/GFF/CoordinateModification.lean:1139`),
which uses Leonardo Bonanno's normalized whole-plane GFF construction. Let
`Q = lqgQ γ = 2 / γ + γ / 2 > 0`, `rₙ = exp (-n)`, `Bₙ = hcirc rₙ 0`, and
`gₙ = affinePairing hC hcirc (rₙ : ℂ) 0`. Set
`Xₙ = 𝔇 (hC ω) 0 rₙ` and `Yₙ = 𝔇 (gₙ ω) 0 1`.

1. The proved `wholePlaneGFFAffineInvariance_univ`
   (`Proofs/Sec3/DerivedInputAssembly.lean:55`) gives that each normalized
   `gₙ` is a project whole-plane GFF. The proven
   `IsWholePlaneGFF.ae_normalized_affine_baseMetric`
   (`Proofs/Sec11/NormalizedBaseMetric.lean:31`) combines coordinate change,
   simultaneous constant Weyl scaling, and nonnegativity to give, for each
   fixed `n`, the almost-sure identity
   `Xₙ = exp (ξ * (Bₙ - Q * n)) * Yₙ`. This statement is about the actual
   pairing functionals, not assumed samplewise distribution representatives.
2. The metric map is measurable in the test-pairing sigma algebra. Therefore
   the normalized GFFs have the same law after applying its fixed evaluation,
   as follows from `exists_common_observable_of_distribution_measurable`
   (`Proofs/Sec11/LQGBaseMetricObservable.lean:14`) and
   `IsWholePlaneGFF.identDistrib_observables_across_spaces`, or from the
   continuous-distance decoder in the same file. Hence `Yₙ` has the fixed
   law of `Y = 𝔇 (hC ω) 0 1`. Metric separation and finiteness give
   `0 < Y < ∞` almost surely. No independence between `Bₙ` and `Yₙ` is needed.
3. The centered circle-average covariance gives `Var(Bₙ) = n`, so Chebyshev
   gives `Bₙ / n → 0` in probability. Since the `Yₙ` have the same positive,
   finite law, `log Yₙ / n → 0` in probability by tightness of this fixed
   real law. Thus `log Xₙ / n → -ξ Q` in probability (all `Xₙ` are positive
   on a common event obtained by intersecting countably many good events).
4. Euclidean topology of the base metric implies `Xₙ → 0` almost surely.
   If `ξ < 0`, step 3 instead implies `Xₙ → ∞` in probability, a
   contradiction. If `ξ = 0`, step 1 gives `Xₙ = Yₙ`, so `Xₙ` has the
   fixed strictly positive law of `Y`, contradicting convergence to zero in
   probability. Therefore `0 < ξ`.

Only positivity of `γ` is used to make `Q > 0`; `γ < 2` is not needed for
this sign argument. The GFF existence prevents a vacuous use of the universal
metric axiom. The calculation is consistent with the exact random-constant
normalization and does not require independence or moments of metric values.

## Refutation checks and remaining work

The E55 witness `exists_projectWholePlaneGFF_ae_euclidean_metric_extension`
(`Proofs/GFF/UnrepresentableGFFExistence.lean:52`) proves that a particular
extension scheme evaluates to Euclidean distance on a pathological GFF version.
It does **not** prove that this extension satisfies `IsLQGMetric`: coordinate
change would require Euclidean distance between `r*u` and `r*v` to agree with
the distance evaluated at the transformed field, which a constant Euclidean
fallback gives as `r * dist u v = dist u v`. For `r ≠ 1` and `u ≠ v` this
fails whenever both relevant evaluations use that fallback. One cannot assume
the transformed field uses it without checking that fact; either way E55 alone
does not supply the required all-axioms counterexample. Likewise reflection
of the field changes the sign of the `Q log r` coordinate shift and does not
directly turn a positive-exponent metric into a negative-exponent metric.

The exact unproved Lean target is:

```lean
∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
  0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 → 0 < ξ
```

Formal work remains to assemble the fixed-distance law, the concentric-circle
variance and convergence-in-probability/tightness argument, and the topology
contradiction using the existing scaling identity. No claim is made that the
displayed Lean target currently compiles. In particular, the hypothesis
`0 < ξ` at `Proofs/Sec11/CorrectedPinchConditionalPositive.lean:16` remains
undischarged in Lean. The minimal operator decision is whether to prioritize
formalizing this derived bridge against the frozen interface or to continue
using the already staged physical-exponent successor while it is formalized;
neither route requires an added literature input. The wider metric mismatch and
E55 version-aware repair remain separate pending operator matters.

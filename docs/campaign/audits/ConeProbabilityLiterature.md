# Lemma 11.8 conditional export handoff

This is a provider handoff, not independent author approval or admission of
literature sources. `ConeProbabilityLiterature.lean` applies the exact two
exports; its first consumer expands the frozen `ConeBadEventProbabilityStmt`
and retains all three fully quantified hypotheses. The staged propositions in
`HarmonicBalls/Proposed/LQG.lean` await operator source-check. In particular,
the fact that Lean checks a conditional implication does not establish the
literature hypotheses.

## Inputs and source pointers

- `hDG`: `∀ Ω [MeasurableSpace Ω] P γ hC hcirc,
  WholePlaneLQGBallMassBounds P γ hC hcirc`. Proposed source: Ding–Gwynne,
  arXiv:1807.01072, Lemma 3.8, p. 25.
- `hCC`: `∀ Ω [MeasurableSpace Ω] P γ hC hcirc,
  LQGMeasureCoordChange P γ 0 hC hcirc`. Proposed sources: Duplantier–Sheffield,
  Proposition 2.1, p. 13, and Sheffield–Wang arXiv:1605.06171, Theorems 1.1
  and 1.4, p. 3; the simultaneous affine formulation needs source review.
- `hE`: `∀ Ω [MeasurableSpace Ω] P γ α hC hcirc,
  LQGMeasureExistence P γ α hC hcirc`. Proposed sources: Duplantier–Sheffield,
  Proposition 1.1, p. 5, and Berestycki–Powell arXiv:2404.16642v2,
  Theorem 2.1, p. 62; whole-plane and singularity extensions need source review.

The exact elaborated Lean types, including universe and measurable-space
quantifiers, are in the audit consumer. The second export instead assumes the
derived `WholePlaneScaledBallMassStep`, `LQGVolumeGrowthAllScalesStmt`, and
the same fully quantified existence hypothesis. These first two are not hidden
inputs of the literature export: `ConeProbabilityFromLiterature.lean` derives
them, using the proved affine invariance, mixture, Weyl scaling, nonatomicity,
and volume-growth assemblies. No additional logical hypothesis was found in
the checked export; this is not a source audit of those assemblies.

## Quantifiers and event

For each γ, α₀, cone Q and M satisfying the frozen hypotheses, p is chosen
before the realization, measure and z; only then may N depend on those objects
and z, and the bound is required for every n ≥ N. The assembly chooses N = 0.
Its universal witness proves the stronger separated-annulus condition with
`r / 100 ≤ infDist`; the frozen strict `<` is passed via `le_of_lt`. It first
chooses a reference realization if one exists; otherwise the realization
quantifier is vacuous. The reference positive ENNReal probability is truncated
and converted to a real p strictly between 0 and 1.

The conclusion is inner-measure form: a measurable A is contained in the cone
event and has probability at least `ENNReal.ofReal p`. The proof obtains A from
null measurability; it does not assume the event itself is measurable.

## Used proof chain

- `coneBadEventProbability_of_literature` →
  `coneBadEventProbability_of_existence` →
  `cone_singular_universal_measurable_witness`.
- The universal witness invokes `cone_unit_event_positive`,
  `cone_ordinary_event_probability_eq_reference`,
  `exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal`, and
  `exists_cone_measurable_subset_of_singular_weight` directly. The ordinary
  equality uses translation, dyadic dilation, and equality across realizations.
- `exists_cone_mass_green_thresholds` uses
  `ae_cone_annulus_mass_pos` and finite Green potential. The former uses
  `ae_fullSupport_all_singular_limits`: its proof actually has an ordinary
  limit μ₀ and an arbitrary actual singular limit μ, compares them away from
  zero, and transfers full support from μ₀. It does not infer existence of a
  singular limit merely from full support; the limit hypothesis is explicit.
- `cone_unit_event_positive` chooses a nonnegative bump, constant on the inner
  annulus and zero on the Green annulus, then uses the measurable local decoder
  and `cone_event_pos_of_smooth_shift`. The latter applies
  `IsWholePlaneGFF.local_smooth_shift_pairing_law` in
  `Proofs/Sec8/WholePlaneSmoothShift.lean`, which uses Leonardo Bonanno's
  Gaussian Cameron–Martin theorem in
  `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. The fixed-shift decoder
  also builds on Bonanno's Lattice-Probability development. This code is used
  through the lean-v4.35 Lattice-Probability dependency, not vendored.
- The cofinal family `Q(γ) - 1/(k+1)` supplies actual auxiliary limits for
  simultaneous representation. The supplied singular limit and the auxiliary
  ordinary limit are compared away from zero. On the separated annulus the
  singular weight exponent is `e = -(γ * α₀)` and its oscillation is bounded
  by `1201 ^ |e|`; the event comparison uses the squared factor, so the
  ordinary threshold is `M * (1201 ^ |e|)^2`. This is parameter-dependent,
  independent of center and scale, and does not assume a universal Weyl bound.

## Kernel audit

`#print axioms` for both exports reports only `propext`, `Classical.choice`, and
`Quot.sound`. This certifies the stated conditional implications, not the
pending source hypotheses or independent correctness of the paper proof.

# GFF raw pairing and sampled-root representation audit

Audit scope: `HarmonicBalls.IsWholePlaneGFF` in `HarmonicBalls/Defs/GFF.lean:93–109`, as used in Section 8, and the two owned audit artifacts. Inspected at repository HEAD `a9ad5a58477b4b59a28e37cae602ec973c780847`; GFF file SHA-256 `c83b244c37e48e0ae2bc6919ce31c080d5ddf3189206828bd0e3fef6c2184132`, corrected TeX SHA-256 `8fdbb03043011800560e4d947eb79a3cfdd7cc8767a3af94469f04201b7593fc`. The operator freeze list `docs/campaign/FROZEN.md` identifies numbered Draft statements, not an independently versioned manifest entry for this definition. This is a scoped representation audit, not approval of the definition or closure of any numbered result.

## Source and binder inventory

Corrected TeX 355–365 calls the GFF a centered Gaussian *random generalized function*, gives covariance and normalization, and introduces circle averages. Lines 380–383 introduce the deterministic logarithmic shift. Lines 395–399 introduce the LQG measure as a limit of circle-average approximations. Lines 2209–2224 use a root sampled from a reweighted LQG measure, a distribution modulo constants, local absolute continuity, and locality of the measure event. The requested representation question is whether the actual raw map is itself a generalized function on one common event, rather than merely having a distribution-valued modification.

The entire declaration's outer binders and six fields are:

| Binder / field | Exact scope and role | Source relation |
|---|---|---|
| `{Ω : Type*}`, `[MeasurableSpace Ω]` | implicit sample carrier and instance | typing |
| `P : Measure Ω` | law, explicit; probability is derived using Gaussian-process field | typing/law |
| `hC : Ω → (ℂ → ℝ) → ℝ` | explicit, raw pairing indexed by *all* functions | candidate field, TeX 356–359 |
| `hcirc : Ω → ℝ → ℂ → ℝ` | explicit, circle process | TeX 362 |
| `measurable_pairing` | `∀ φ, IsTestFunction univ φ → Measurable (fun ω => hC ω φ)` | fixed-test measurability |
| `measurable_circle` | `∀ r z, 0 < r → Measurable (fun ω => hcirc ω r z)` | fixed circle measurability |
| `isGaussianProcess` | process on the subtype of admissible pairing/circle observables; finite families Gaussian | joint fixed-observable law |
| `integral_eq_zero` | every admissible observable has integral zero | TeX 356 |
| `covariance_eq` | every pair of admissible observables has smeared covariance `wholePlaneGFFCov` | TeX 358–359 |
| `ae_continuousOn_circle` | one full-measure event for continuity of `(r,z) ↦ hcirc ω r z` on `Ioi 0 ×ˢ univ` | circle-average modification |

`IsTestFunction U φ` expands to `ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U` (`Defs/Laplacian.lean:47–48`). Admissible pairings require `U = univ`; circles require positive radius (`Defs/GFF.lean:44–56`); covariance is the iterated smearing of `wholePlaneCov` (`:34–40, 63–78`). There is no explicit field asserting samplewise linearity, continuity, simultaneous test-function equality, or raw joint measurability in a random test. Circle continuity is not continuity of `hC ω` as a functional. The record **syntactically omits** a samplewise representation field; whether its six actual properties nonetheless imply such representation is an unresolved mathematical implication, not a proved failure of implication or a counterexample. The abstract diagonal example in `RawRecenteredPairing.lean:95–108` does not construct a realization satisfying these six fields and therefore cannot establish a source mismatch. No genuine semantic mismatch is proved in this audit.

## Existing versions and consumers

* `MeanZeroDistributionVersion.lean:16–25,44–72` reconstructs a measurable distribution and proves `∀ φ : TestC0, H(ω)(φ) = hC ω φ` almost surely, **for each fixed test separately**. `TranslatedDistributionInsertion.lean:108–125` identifies this particular canonical reconstruction at each fixed mean-zero test. Quantifiers do not automatically commute for uncountably many tests.
* `RecenteredVersionIndependence.lean:19–85` uses only countably many fixed tests to identify the reconstructed distribution modulo its gauge with any distribution-valued fixed-test version. Consequently its recentered observation equals the translated pairings of that **version** for all roots and local tests on one event. It does not identify the raw translated evaluation.
* `CanonicalPhaseCertificate.lean:20–74` proves a measurable phase/field event is determined by countably many coordinates and that coordinatewise a.e. equality plus process measurability gives equality of joint cylinder laws. `:78–94` applies this to unshifted local pairings and a measurable companion. These fixed-coordinate cylinder comparisons do not evaluate raw `hC` at a root-dependent test.
* `RecenteredRootedObservation.lean:32–82` maps the **reconstructed** observed-root cylinder law into an origin-insertion comparison. It assumes the exact unnormalized `hrooted` absolute continuity at `:64–68`, in addition to measurability, finite mass and the geometric side condition. `RootedUniformPhaseCertificate.lean:23–41,55–78` consumes this rooted-law assumption and produces sampled-root phase-event membership for the reconstruction and, separately, for each distribution-valued fixed-test version. The reference event's frequency interpretation is for the reference measure.
* `RawRecenteredPairing.lean:19–33` proves samplewise agreement of canonical reconstruction with **every** mean-zero raw test iff that sample's raw mean-zero pairing is represented by a distribution. Its `:34–90` uses the explicit stronger `hrep : ∀ᵐ ω ∂P, ∃ H : DistC, ∀ φ : TestC0, H φ.1 = hC ω φ.1` to identify all raw translated pairings, obtain map equality for any kernel, and transfer the normalized comparison. This is a sufficient premise of that theorem, not a proved necessary premise for the comparison or for Lemma 8.2.
* `CanonicalRootedApproximation.lean:20–34,65–88` constructs decoders from a fixed-test distribution version and the root for buffered centered circle-average approximants. `CommonCanonicalRootedApproximation.lean:20–55` constructs reference approximants `f` and sampled-root approximants `g`; they are **two sequences on different inputs**, and does not identify `f` on the recentered local field with `g` on `(H, z)`. `RootedCommonMassApproximation.lean:40–48` displays the stronger common-decoder identity `hFμ` needed for that route. `RootedJointObservedFrequency.lean:32–41` offers a different route via an explicit joint field/circle domination `hdom`. These measure-decoder/joint-law leaves are distinct from equality of raw random-test pairings.

## Checked bridges and exact remaining implications

`HarmonicBalls/Audit/GFFSamplewiseRepresentation.lean` proves:

1. `ae_ae_eventually_raw_phase_events_of_countable_coordinates`: for each scale a specified countable family of local tests determines the event, and for each selected test separately reconstruction agrees with raw translation at `P`-a.e. field and `μ ω`-a.e. root in `A`. Existing reconstructed event membership then transfers to the raw observations at eventually all scales. The countable family, event invariance, sampled-root agreements and reconstructed event are explicit premises; no raw-process measurability or samplewise `hrep` is assumed. By the existing `eq_preimage_restrict_countable` argument in `CanonicalPhaseCertificate.lean:20–58`, measurable cylinder events have countable coordinate dependence; the new theorem itself takes the selectors and invariance as hypotheses.
2. `map_rooted_recentered_observation_eq_raw_of_ae_sampled`: a common equality for the local tests only at `(P ⊗ₘ κ)`-a.e. sampled root suffices for equality of the two joint mapped laws. This assumes neither agreement at other roots nor representation on all mean-zero tests.
3. `IsWholePlaneGFF.map_rooted_recentered_observation_eq_raw_of_coordinatewise`: the **weaker** per-local-test `P ⊗ₘ κ` a.e. agreement plus measurability of the raw translated cylinder process suffices for the same joint law. The companion root is retained. Apply the normalized reconstructed comparison after rewriting by this equality. The lemma does not derive the per-test agreements from `hh`.

The exact conditional law-bridge leaves, for the particular `κ := weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const` and `U := ball 0 r`, are:

```lean
Measurable (fun p : Ω × ℂ => fun φ : Section6.LocalTest U =>
  hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1))

∀ φ : Section6.LocalTest U,
  (fun p => recenteredDistributionObservation U
    (Section6.pairingProc hC p.1, p.2) φ) =ᵐ[P ⊗ₘ κ]
  (fun p => hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1))
```

The fixed-test version theorem controls `hC ω ψ` for each deterministic **global** `ψ`; it does not itself control the above field-dependent test `testAffinePull 1 p.2 φ.1.1`. Nor does it give joint measurability of that raw evaluation. It remains open here whether these leaves follow from the actual six fields together with the relevant LQG/root assumptions. An independent proof of the joint local law or a common measurable measure decoder could avoid both raw leaves; the audit makes no necessity claim.

The separate rooted-law leaf is the exact displayed `hrooted` in `RecenteredRootedObservation.lean:64–68`. The operator's pending source review for the DMS21 whole-plane rooted formula is recorded in `~/paper-fleets/hb/INPUT-REQUESTS.md:58–102`; it is neither staged nor asserted here. The additional source-to-Lean local decoder/measure identification is not discharged by equality of fixed-field cylinder laws alone. See E48 in `~/paper-fleets/hb/ESCALATIONS.md` for current campaign status. No new literature input is introduced.

## Verification and attribution

The audit Lean module uses Leonardo Bonanno's distribution-valued GFF development in `LatticeProb.Bonanno.LQGMetric.Field.MarkovGerm`, `RandomDistVersion`, `GFFLaw`, `ExistGFF`, and `GFFInvariance` through the existing Section 8 modules. The `#print axioms` output for each new theorem is `propext`, `Classical.choice`, and `Quot.sound`. `lc` and `lb` are required for this audit module; the owned Lean file has no forbidden placeholders. The findings do not establish the raw-law leaves, the common decoder, E48, or any numbered result.

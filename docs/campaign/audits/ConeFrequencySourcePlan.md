# Lemma 11.8 to Lemma 11.7: cone frequency source plan

Task `cone-frequency-source-plan`, 2026-11-06. This is a conditional proof
plan, not a Lean proof or a new input. Take the **entire frozen**
`ConeBadEventProbabilityStmt` (`Draft/Section11.lean:185`) as a hypothesis.
Its inner-measure form, existential `N(z)`, and order of binders matter.
The target is `ManyConeBadScalesStmt` (`Draft/Section11.lean:173`).

## Constants and the reference event

Fix γ, α₀, Q, M in the order and with the hypotheses of the target. Prove
`γ < lqgQ γ` from `0 < γ < 2`. Invoke 11.8 with **α = γ**, the same γ,
the same oriented cone Q and the same M; obtain `p ∈ Ioo 0 1` before
choosing a probability space. Set `δ = p / 2`. It is in `(0,1)` and is
uniform across all target spaces, fields, roots and N. It may depend on γ,
Q and M (and hence is admissible after the target's α₀ binder); no
uniformity over arbitrary γ, α₀, Q or M is established or needed.

For any reference GFF and its γ-inserted LQG measure ν, let `r n = 2⁻ⁿ`
and `E n = {ω | coneMassEvent (ν ω) Q M (r n) 0}`. At z=0,
`infDist 0 (annulus 0 r (6*r)) = r` for r>0, even though the annulus is
open. Prove this real metric fact, and `r/100 < r`. The predecessor gives
some `N₀` and, for every `n ≥ N₀`, a measurable `A n ⊆ E n` with
`ofReal p ≤ P (A n)`. This is sufficient even before `E n` is shown
measurable. In particular the n=0 event is **not** directly bounded by the
predecessor. Once E n has a measurable or null-measurable version and the
whole indicator path is stationary, its common probability `q` satisfies
`q ≥ p` by taking any n ≥ N₀. Thus δ < q; no estimate deteriorates
under the later absolutely continuous changes of law, because those changes
are applied to one probability-one tail event, not to individual scales.

## Reference frequency, with exact available producers

The needed stationarity is equality of path laws, not equal one-scale
marginals:

```lean
IdentDistrib (fun ω n => if coneMassEvent (ν ω) Q M (r n) 0 then (1 : ℝ) else 0)
  (fun ω n => if coneMassEvent (ν ω) Q M (r (n+1)) 0 then (1 : ℝ) else 0) P P
```

Derive it from dilation covariance of the actual cone event and the law of
the normalized dyadic measure path. `IsWholePlaneGFF.identDistrib_localizedDyadicMeasure_shift`
(`Proofs/Sec8/LocalizedNormalizedMeasurePath.lean:96`) supplies the latter,
**conditionally** on `WholePlaneGFFAffineInvariance P hC hcirc` and
`LQGMeasureCoordChange P γ γ hC hcirc`, staged in `Proposed/LQG.lean:49,108`;
those are not consequences merely of the two frozen target hypotheses in the
current interface. Pick U = ball 0 7, so all event supports lie strictly
inside U at unit scale. Establish dilation of the cone from `IsCone`,
translation and scaling of annuli, and Green potential covariance, including
the zero/infinite measure cases needed by the statement. The Green dilation
producer is `Steps/Sec11/AnnulusGreenDilation.lean:63`; the cone-event
packaging remains to be checked/proved. For actual LQG samples, normalize by
a positive finite U mass: `coneMassEvent_normalizedRestriction_iff`
(`Proofs/GFF/ConeMassLocalRepresentation.lean:48`) and
`coneMassEvent_smul_iff` (`Proofs/GFF/FixedShiftCircleLQGRepresentation.lean:443`).
Full support `LQGMeasureFullSupportStmt` (`Draft/Section2.lean:109`), a
separate literature statement, plus local finiteness gives positivity and
finiteness. Distinguish a.e. path equality from pointwise equality.

For each Q, prove its Borelness from the open-or-complement definition
(`Defs/Geometry.lean:149`) and the translated cone's Borelness; then
`measurableSet_coneMassEvent` (`ConeMassLocalRepresentation.lean:40`)
gives measure-space event measurability. The actual random measure needs an
a.e. measurable version and the path needs an a.e. local version in every
`Section6.fieldSigmaAlgebraModConst γ hC (ball 0 ε)`; these must match the
actual ν simultaneously for countably many n. Available producers are
`IsWholePlaneGFF.exists_buffered_normalizedRestriction_of_fullSupport`
(`Proofs/Sec8/BufferedNormalizedRestriction.lean:55`) and
`ae_local_localizedDyadicMeasure_of_buffered_versions`
(`Proofs/Sec8/LocalizedPathBufferedLocality.lean:35`). The latter works with
a smaller ball inside the requested germ ball; do not assume exact
same-radius restrictions. `coneMassEvent_iff_of_restrict_eq`
(`ConeMassLocalRepresentation.lean:21`) gives locality to ball `0 (6*r n)`;
use a strictly larger buffer where needed. Countable encoding is already
provided by `exists_coneMassEvent_countable_encoding` (same file:155),
conditional on a generating pi-system and cone Borelness.

The required zero-one statement is exactly
`IsWholePlaneGFF.origin_germ_trivial` (`Proofs/Sec8/OriginGermZeroOne.lean:82`):
every set measurable in every positive-radius field-modulo-constants σ-algebra
has P-measure zero or one. With path stationarity and a.e. local versions,
`ergodic_shift_of_stationary_ae_local_germ`
(`Proofs/Sec8/GermPathErgodic.lean:17`) supplies ergodicity; its specialized
normalized-measure path variant is
`IsWholePlaneGFF.ergodic_localizedDyadicMeasure_shift_of_fullSupport`
(`LocalizedPathBufferedLocality.lean:141`), still conditional on the affine,
coordinate-change and buffered-version hypotheses. Birkhoff is provided by
`pointwiseBirkhoff_of_latticeProb` (`Proofs/Sec8/BirkhoffPort.lean:18`,
using `LatticeProb.ae_tendsto_bAvg`). Specialize it to the bounded cone
indicator, and use `eventually_goodScale_block_ncard`
(`Proofs/Sec8/BlockFrequency.lean:66`): if prefix means tend to q then block
means tend to `2q − q = q`; δ < q gives eventually at least δN successes in
`[N+1,2N]`. `PinchNormalizedUnitFrequency.lean:16` is a nearby positive-event
template, but its δ depends on P; here use the uniform p above instead.
Section 8's `origin_many_good_scales_of_positive_threshold`
(`PositiveThresholdOriginAssembly.lean:21`) is not this theorem: it uses a
small **failure** probability and a different event. No frequency statement
is assumed as an input.

## Rooted transfer and phase

For each target field h = H − α₀ log|·|, let λ = μ_H. On B₁ sample a root
from λ restricted to B₁ normalized by its mass. The marked insertion formula
in DMS Lemma A.10 ([arXiv:1409.7055v4, PDF p. 184](https://arxiv.org/pdf/1409.7055v4#page=184))
and the local Cameron–Martin comparison of
[Miller–Sheffield Proposition 2.9](https://arxiv.org/pdf/1302.4738v2#page=49)
motivate the transfer; neither field-law statement alone proves the actual
joint field/GMC-measure comparison required here. Use the local projective
observation and the exact proposed domination displayed in
`docs/campaign/audits/LocalRootedComparisonRepair.md:35`: actual recentered
restrictions normalized by a positive finite local mass, with z retained.
On each member of a countable buffered cover of B₁ excluding 0 and the unit
circle, its right-hand reference is independent z and ν for H − γ log|·|.
The proof must construct the jointly measurable actual observation, prove
the marked joint GMC identity, local domination after smooth cutoffs and
translation modulo constants, and match both actual measures to a common
local decoder. DMS supplies a field insertion description; it is not by
itself the repository's asserted measure-level domination. These are derived
obligations, not newly postulated literature inputs. Compare λ and μ via
Weyl scaling, and remove exceptional roots using the marked formula,
non-atomicity and positivity/finiteness as appropriate.

Unlike Section 8's anchored lattice event, the cone event has **no lattice
phase**: recentering sends Q(z) to the same fixed Q, not a rotating or
translated direction; positive real dilation preserves Q. Hence no torus
doubling or uniform-phase certificate is required. Prove the exact
translation identity for both the mass and Green supremum; the available
`GreenTranslation.lean:67,86` is a starting point, not yet a cone-event
identity. The target's fixed Q is retained for every root; there is no
uncountable intersection over cones. For a fixed buffered local observation,
all sufficiently large n lie within its window, so the countable eventual
block-frequency event is determined by that observation, using
`coneMassEvent_iff_of_restrict_eq` and positive-finite normalization. Transfer
the *whole* reference a.s. tail event by domination and Fubini, then recover
μ-a.e. roots. Scale/translate the bounded-root argument over a countable
cover of ℂ, checking the pinned normalization and α₀ insertion under each
change of coordinates and retaining the same p and δ. Alternatively prove
the marked formula directly on each bounded set; do not simply assert that
scaling preserves the pinned field without the additive normalization.

## Conditional leaves and status

1. Derive Borel cone/translation/dilation identities, Green covariance,
   `infDist` at the origin, and the measurable countable tail event.
2. Supply the stated affine-invariance and LQG coordinate-change inputs,
   full support, and their universe/source matching; construct the a.e.
   normalized local versions and stationary actual indicator path. The
   existing producers above are conditional, not unconditional closure.
3. Prove the marked joint field–GMC observation domination and its
   measurable normalization, local-to-global transfer, Weyl comparison,
   and null exceptional sets. The exact proposed measure-domination type is
   in the linked local-rooted audit; its source matching remains open.

These are precise formal/source obligations in the printed reduction, not a
counterexample to the paper. In particular, 11.8 does apply at the origin:
the annulus avoids 0 although its center is 0. No new proposed input, Lean
declaration, or closure of either numbered result is claimed here.

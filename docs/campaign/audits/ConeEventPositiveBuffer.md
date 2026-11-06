# Cone-event positive buffer: source proof and handoff

Task `cone-event-positive-buffer-source-proof`, 2026-11-06. This is a mathematical
handoff, not a compiled Lean theorem or an admitted input. All proposed types
below are **uncompiled**. The frozen event is `Draft/Section11.lean:72`; its
Green functional is an extended integral, infinite on the diagonal. The
conclusion of `ConeBadEventProbabilityStmt` quantifies `p` before the carrier.
The local positive-buffer argument does not itself discharge that uniformity.

## Geometry, including complements

Let `A = annulus 0 1 2`, `D = annulus 0 3 6`, and `T = A ∩ coneAt Q 0`.
For every `IsCone Q`, `T` is Borel and contains a nonempty open ball. For an
open cone choose a nonzero point in it: openness supplies one, and positive
dilation puts it strictly between radii 1 and 2. For a complementary cone,
write the open sector as `{c v + d w : c,d > 0}`. Openness and nonemptiness
force `v,w` to be linearly independent over ℝ: otherwise the sector lies in
a line, which has empty interior. In the linear coordinates given by `v,w`,
the open negative quadrant lies in its complement. Dilate any point of that
quadrant to norm 3/2. This also proves Borelness: the open cone is open and
its complement is closed. This argument does not assume `Q` itself is open.

## Actual positive and finite observables

Fix `0 < γ < 2`, `α₀ < lqgQ γ`, one whole-plane GFF and an actual
`IsLQGMeasureOfField` limit `μ`. Put `X = μ T` and
`Y = annulusGreenPotentialSup μ 0 3 6`. Both are a.e. measurable: use
`IsWholePlaneGFF.aemeasurable_lqgMeasure`, measurable evaluation on Borel `T`,
and `measurable_annulusGreenPotentialSup` (`Steps/Sec11/PinchGreenMeasurable.lean:42`).
Use measurable representatives, not an unjustified assertion that the given
versions are measurable on an incomplete probability space.

* `X > 0` a.s. by full support and the ball in `T`. This follows from
  `Section6.ae_fullSupport_all_singular_limits`
  (`Proofs/Sec6/SimultaneousSingularMeasure.lean:155`), with
  `WholePlaneScaledBallMassStep` and `LQGMeasureExistence P γ 0 hC hcirc`;
  both are conditional source obligations, not unconditional Lean facts.
  Alternatively use `LQGMeasureFullSupportStmt` (I1), when supplied.
* `Y < ∞` a.s. by
  `ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth`
  (`Steps/Sec11/PinchGreenFinite.lean:50`) with I2
  `LQGVolumeGrowthAllScalesStmt` (`Draft/Section2.lean:122`), `a=3`, `b=6`.
  Its proof uses volume growth to eliminate atoms and control the logarithmic
  singularity uniformly in the pole; local finiteness alone does not suffice.
  I2 is a derived statement whose staged scaled-ball estimate still needs
  source admission. As an alternative, the Green clause
  `GreenPotentialHolderStmt` (`Draft/Section2.lean:190`) for the disk of
  radius 6 and `f=1`, together with non-atomicity, integrability, and
  nonnegativity of the disk Green kernel, bounds the extended annular integral
  by a continuous potential on the compact closed disk. One must explicitly
  handle the diagonal; the existing volume-growth theorem already does so.

Since the law is a probability, choose positive integers `j,k` so that the
measurable representatives satisfy `X ≥ (j:ℝ≥0∞)⁻¹` and `Y ≤ k` jointly
with positive probability (indeed probability at least 1/2 is attainable).
Intersect with a measurable conull set on which the representatives equal
the actual values. Thus there are deterministic finite `C₁,C₂ > 0` and a
measurable `G` with `P G > 0`, `ofReal C₁ ≤ X`, and `Y ≤ ofReal C₂` on `G`.
These constants initially depend on the chosen realization and on
`γ,α₀,Q`; there is no claim of carrier-uniformity here.

## Bump and actual-limit inclusion

Choose `χ ∈ C_c^∞(ℂ)` with `0 ≤ χ ≤ 1`, `χ=1` on the compact closed
annulus `{1 ≤ |z| ≤ 2}`, and support in `{1/2 < |z| < 5/2}`. Such a
cutoff follows from the smooth bump construction on Euclidean space (e.g.
Mathlib `Analysis/Calculus/BumpFunction/Basic.lean`). Set
`H = max 0 (log (M*C₂/C₁) / γ)` and `g = H χ`. Then `g ≥ 0`,
`exp (γ H) C₁ ≥ M C₂`, and `g=0` on `D`. This positive part corrects the
printed choice, which can be negative; alternatively decrease `C₁` first.

For every sample where the dyadic profiles are continuous and `μ` is the
actual limit, define `ν = μ.withDensity (fun x => ofReal (exp (γ*g x)))`.
The continuity follows from the GFF circle-process continuity and
`fieldCircleAverage`; `isLQGLimit_addCircleAverage`
(`Proofs/Sec6/LQGWeylScaling.lean:79`) proves that `ν` is an **actual**
limit for `addCircleAverage (fieldCircleAverage α₀ hcirc) g`, not merely a
formal Weyl expression. On `T`, `ν T = ofReal (exp (γ H)) * μ T`; on `D`,
the restrictions of `ν` and `μ` are equal, so the full extended integral,
including its diagonal and the supremum, is unchanged. Hence on `G` and the
conull actual-limit event,
`ofReal M * annulusGreenPotentialSup ν 0 3 6 ≤ ν T`, exactly
`coneMassEvent ν Q M 1 0`. No division or cancellation of infinite values
is used. If an independently given shifted actual limit is used instead,
first invoke uniqueness of locally finite vague limits to identify it with ν.

An exact consumer-shaped statement to implement, with hypotheses expanded as
above rather than added as a literature input, is:

```lean
-- UNCOMPILED; variables and instances as in the cited theorems.
∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
  ∃ G : Set Ω, MeasurableSet G ∧ 0 < P G ∧
    ∀ ω ∈ G, ENNReal.ofReal C₁ ≤ μ ω (annulus 0 1 2 ∩ coneAt Q 0) ∧
      annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal C₂
```

The inclusion is an a.s. implication, because the original actual-limit and
profile-continuity conditions are a.s.; do not demand it for junk values.
For a transfer choose `6 < L < R`, apply
`IsWholePlaneGFF.exists_enclosing_fixedShift_coneMassEvent_representation`
(`Proofs/GFF/ConeMassLocalRepresentation.lean:334`) with full support and
the actual shifted limit. It yields one measurable local pairing event for
both limits. The matching local deterministic log insertion is `k φ =
-α₀ * ∫ x, φ x * log ‖x‖`; take `k=0` when working directly with the
uninserted field. Apply `cone_event_pos_of_smooth_shift`
(`Proofs/Sec11/ConeBadEventTransfer.lean:55`). The smooth-shift law uses
Leonardo Bonanno's Gaussian Cameron–Martin theorem, as credited there.
The representation gives a measurable preimage equal a.s. to the event;
intersect it with a measurable conull equality set to obtain the frozen
statement's measurable subset, rather than assuming completeness.

## Uniformity obstruction and affine handoff

The local proof provides a strictly positive number for each carrier; taking
their infimum is invalid. A sufficient precise missing formal bridge is:

```lean
-- UNCOMPILED derived lemma, NOT a proposed literature input.
theorem actual_lqg_measure_law_unique
    (h₁ : IsWholePlaneGFF P₁ hC₁ hcirc₁)
    (h₂ : IsWholePlaneGFF P₂ hC₂ hcirc₂)
    (m₁ : IsLQGMeasureOfField P₁ γ α₀ hcirc₁ μ₁)
    (m₂ : IsLQGMeasureOfField P₂ γ α₀ hcirc₂ μ₂) :
    P₁.map μ₁ = P₂.map μ₂
```

Here the carriers may have different measurable spaces and universe levels;
all functions and measures have their indicated implicit types. A weaker
equality of the laws of the measurable normalized cone/Green observable also
suffices. Derive, do not assume, this identity from equality of the joint
Gaussian laws of the admissible circle coordinates, continuity from a
countable dense space-time set, measurable dyadic approximation integrals,
and uniqueness of the actual vague limit on a countable determining class.
The local decoder `ConeMassLocalRepresentation.lean:334` chooses its radius,
continuity sets and event after seeing the carrier; its existence alone does
not assert this cross-carrier identity. Once the identity and existence of one
reference realization are proved, its positive probability gives a single
`p∈(0,1)` for all carriers. This is a precise implementation obligation,
not a claim that the paper's probability statement is false.

For the full scale/centre result, the uninserted event also needs the staged
`WholePlaneGFFAffineInvariance` and actual LQG limit covariance plus the
deterministic affine identities and nonzero finite normalization premises in
`audits/ConeEventAffineIdentities.md`. For `α₀ ≠ 0`, Weyl comparison away
from zero gives factor at least `1201^(-|γ*α₀|)` under the frozen distance
condition, as calculated in `GAPS-HB-1106.md`; it is not universal over the
field parameters. The singular origin itself is handled directly by the
positive-buffer argument for every admissible `α₀`, or by the correct origin
scaling law, not by an assumed smooth logarithm there. Paper line 2840's
nonnegative-bump height and line 2868's universal factor are proposed proof
clarifications (E54), pending operator review; neither refutes Lemma 11.8.

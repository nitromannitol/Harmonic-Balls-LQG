# Section 11, Lemma 11.13 (ManyPinchScalesStmt): closure scales (z3)

Task: `z3-sec11-many-pinch-scales`. Targets: `ManyPinchScalesStmt` (`HarmonicBalls/Draft/Section11.lean:259`, Lemma 11.13,
draft lines 515-664) and `HarmonicBallNotMetricBallStmt` (`Section11.lean:231`, Prop 11.11, draft lines 666-774).
Written argument: `notes/sec11-proof/sec11-proof.tex` (audit `notes/sec11-proof/AUDIT.md`, verdict CORRECT).
Hypothesis taken from z6: `Sec11LocalPinchCertificateStmt` (`HarmonicBalls/Proofs/Sec11/Closure/LocalCertificate.lean:32`),
recorded in `notes/sec11-claims.md`.

## Status

| Piece | Status | Where |
|---|---|---|
| Prefix-to-block average (draft 536-552, `2 A_{2N} - A_N`) | PROVED, standard axioms | `Proofs/Sec11/ClosureScales/CertificateBlockDensity.lean` (`tendsto_block_average_of_prefix_average`) |
| Origin block density for a stationary, germ-trivial family of local certificate events | PROVED, conditional on explicit premises | same file (`frozen_block_density_of_certificate_family`) |
| Uniform rate `δ` chosen before the probability space | OPEN | draft 554-563 |
| Fubini glue of the marked identity: rooted a.s. statements for a.e. root `z` give `μ_ω`-a.e. `z` a.s. (draft 635-649) | PROVED, conditional on the marked identity (explicit hypothesis, DMS21 Lemma A.10 marked version) | `Proofs/Sec11/ClosureScales/RootedTransferGlue.lean` (`ae_ae_of_marked_identity_of_rooted_null`, commit b648d21) |
| Internal pinch origin block density under a stationary, germ-trivial law `Q` (draft 536-563) | PROVED, conditional on the listed Q-level hypotheses | `Proofs/Sec11/ClosureScales/InternalOriginDensity.lean` (`internal_block_density_of_stationary_germ_law`, commit b4a8d2f) |
| Typical-point transfer with the origin hypothesis discharged (draft 565-649) | PROVED, conditional on the rooted comparison families and the Q-level data | `Proofs/Sec11/ClosureScales/TypicalBlockDensityFromOrigin.lean` (`ae_ae_pinch_block_density_of_origin_law`, commit 582ea64) |
| Uniform rate and rooted comparison families for every `Omega` (draft 554-563, 565-634) | OPEN: step `PinchRootedDataStmt` not yet written (next step); needs metric-level comparison `heq` (B3) | draft 554-649 |
| Dyadic extension from `B_1` to `ℂ` | OPEN | draft 649-650 |
| Prop 11.11 from `ManyPinchScalesStmt` | Existing reduction; waits on the line above | `Proofs/Sec11/StagedResultClosures.lean:79` (`harmonicBallNotMetricBallStmt_of_stagedInputs`) |

Nothing here closes a numbered result: `ManyPinchScalesStmt` is not proved (the rate is `Ω`-dependent and the
typical-point transfer is missing), and Prop 11.11 is not proved.

## Proved lemma: `frozen_block_density_of_certificate_family`

Parameters: `P`, `μ`, `D`, `U T Q' Q`, `M`, `z`, a family of certificate events `E : ℕ → Set Ω` with indicators `X n`,
and a germ filtration `germ`. Hypotheses (open steps, not literature inputs):

* `hsub`: `E n ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M (2⁻¹ ^ n) z}` (sufficiency at scale `2^{-n}`; draft 515-530,
  `E_r(z;M) ⊂ Ĝ_r(z;M)`).
* `hXgerm`: `X n` is `germ ε`-measurable for all large `n` (locality of the certificates).
* `htrivial`: the germ σ-algebra is trivial (draft 515-534; mixing of the dilation implies ergodicity).
* `hstat`: the indicator law is stationary under the shift (draft 515-530; scale invariance and the logarithmic drift
  changing only by a constant).
* `hpos`: `0 < P (E 1)` (the scale-`2^{-1}` certificate has positive probability; z6 gives positivity at scale `1`, the
  two agree in law by `hstat`-type scaling; this link is part of building the family and is not yet in Lean).

Conclusion: `∃ δ ∈ (0,1), ∀ᵐ ω, ∀ᶠ N, δ N ≤ #{n ∈ [N+1, 2N] : pinchPointEvent … (2⁻¹^n) z}`.

Proof route: `ae_tendsto_initialScaleAverage_of_stationary_tail_trivial_germ` (`Steps/Sec11/PinchStationaryMean.lean:48`,
generic in `X`), with `pointwiseBirkhoff_of_latticeProb` (LatticeProb, Leonardo Bonanno, via `Proposed/Birkhoff.lean`).
The prefix limit is `∫ X 1 = P(E 1)`. The block average tends to the same limit, and `δ = min(P(E 1)/2, 1/2)` is
eventually below it. The indicator is dominated by the frozen indicator by `hsub`.

Why `δ` depends on `Ω` here: `δ` uses `P(E 1)` for the given `P`. The frozen statement needs `δ` before `Ω`, so this
lemma does not yet give `ManyPinchScalesStmt`.

## Existing chain (for orientation)

* `manyPinchScalesStmt_of_internalFrequency` (`Proofs/Sec11/InternalPinchFrequency.lean:23`) reduces the frozen statement to
  an internal-bounds frequency for all `ξ` (with `LQGMetricFieldAxioms`). That frequency is the open part.
* `ae_eventually_pinchPointEvent_block_ncard_of_stationary_tail` (`Steps/Sec11/PinchStationaryMean.lean:119`) is the origin
  density for the INTERNAL event at `z` (with `hX` tied to `pinchPointEventWithInternalBounds`).
* `ae_ae_pinch_block_density_of_recentered_observation` (`Proofs/Sec11/PinchRecenteredObservation.lean:67`) is the
  typical-point transfer (`∀ᵐ ω, ∀ᵐ z ∂μ ω`). Its premises are the rooted comparisons (`hrooted`, `hac`, `hdom`, `hcomp`)
  and `hfixed`, the origin density under the observed law `Q` for the INTERNAL event.
* The rooted comparison shape is shared with Lemma 8.2 (`Proofs/Sec9/RootedComparisonWeakUniqueness.lean:32`,
  `hcomparison`), which the repository treats as an open proof obligation.
* `Steps/Sec11/PinchLocalDensityTransfer.lean:18` (`ae_eventually_block_density_of_local_absolutelyContinuous`) is generic
  in the event `E` and transfers an origin density across a local absolute-continuity hypothesis.

## Gaps found (exact)

1. **Internal positivity is not supplied by z6's certificate.** `Proofs/Sec11/CorrectedPinchFrequency.lean:26-28` says
   `CorrectedLocalPinchCertificate` asserts no identification with the internal event. The internal-based origin lemmas
   (`Steps/Sec11/PinchStationaryMean.lean:119`, `PinchRecenteredObservation.lean:67`) need `P{pinchPointEventWithInternalBounds …
   (2⁻¹)^1 … 0} > 0`. The gap is `CorrectedLocalPinchCertificate` → internal inclusion, or a decoder from the certificate
   to a set of observations `(μ|_{B_r}, D|_{B_r})`.
2. **Certificate events are field-level sets, not observation-level.** `E ∈ σ(B_7 mod constants)` is not a function of the
   pair `(μ, D)`. The observation-level transfer (`PinchRecenteredObservation`) therefore cannot consume the certificate
   family directly. The gap is a measurable decoder from observations to the certificate (or an internal-to-certificate
   inclusion, see 1).
3. **Uniform rate.** The origin rate `P(E 1)/2` depends on `Ω`. The frozen statement needs one `δ` for all `Ω` (draft
   554-563: the canonical joint law and the metric uniqueness of [DGu] Theorem 1.13 make the constant independent of `Ω`).
   No Lean statement of this canonical-law uniformity exists yet.
4. **Rooted metric for the reference law.** The observed law `Q` in `PinchRecenteredObservation` is the law of `(μ, D)`. Its
   reference (the γ-singular field) needs a metric `D` at exponent `γ`, which the frozen statement does not provide
   (draft 583-634, metric version bridge).
5. **Draft 651-664 is a consumer, not part of Lemma 11.13.** It takes `M = C_H` from Lemma 11.6 for Prop 11.11 (good
   radii). It belongs to the Prop 11.11 chain, where `annulusMassBoundByHarmonicChainStmt_of_stagedInputs` already supplies
   Lemma 11.6.

## Literature inputs used

None new. `pointwiseBirkhoff_of_latticeProb` is a theorem (LatticeProb, Leonardo Bonanno). Distribution-level inputs
(DMS Lemma A.10 marked identity, DGu uniqueness, tail triviality) remain open premises above, not staged in `Proposed/`.

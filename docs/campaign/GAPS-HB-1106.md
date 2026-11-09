# Harmonic-balls mathematical triage, 2026-11-06

## 3. Section 8 global comparison: FALSE

The universally quantified `hcomparison` in `HarmonicBalls/Proofs/Sec8/TypicalPointStatement.lean:34` is false; this does not refute the local comparison used in Lemma 8.2. The detailed source check and counterexample are in `docs/campaign/audits/RootedLawSourceCheck.md`; the proposed local interface and its unresolved joint-law and measurability bridges are in `docs/campaign/audits/LocalRootedComparisonRepair.md`.

Take γ = α₀ = 1, and on a canonical whole-plane GFF probability space take μ = ν to be the LQG measure of h = H − log|·|. This satisfies α₀ < Q = 5/2. For fixed z ≠ 0, the translated field has its pre-existing logarithmic singularity at −z, whereas the field defining ν is locally an ordinary GFF plus a smooth function there. By Berestycki–Sheffield–Sun, *Equivalence of Liouville measure and Gaussian free field*, Theorem 1.1 and Remark 1.2 (arXiv:1410.5407v4, PDF pp. 2–3; local reconstruction in the proof, p. 11), the restricted measure determines the local field. The circle-average slope divided by log(1/r) consequently tends to 1 for the former and 0 for the latter. Local reconstruction on a countable rational-disc basis yields a measurable separating set A_z of measures, jointly measurable in (z, measure), with P[C_z μ ∈ A_z] = 1 and P[ν ∈ A_z] = 0. Here C_z m is the pushforward by v ↦ v − z. The ordinary GFF circle-average slope is zero by the Brownian strong law; the deterministic logarithm contributes one.

For every n, `hac` and `hraw` imply that the reference law assigns zero mass to {(ω,z): C_z μ(ω) ∈ A_z, z ≠ 0}; Fubini uses the joint measurable version above. `hroot` then gives the same zero mass to the weighted rooted law. But that rooted law gives positive mass to the event for some n: the localization sets exhaust the plane, w is positive and finite, and μ is locally finite, non-atomic, and has full support. This is a contradiction. No use of `hdom` is needed. Thus no combination of individual source claims can prove this global interface; in particular `hraw` cannot be inferred from local smooth-shift equivalence. `hac` alone is reflexive if R is the shifted law, but this does not establish `hdom` or `hraw`.

DMS21, *Liouville quantum gravity as a mating of trees*, Lemma A.10, whole-plane paragraph (arXiv:1409.7055v4, PDF p. 184), gives the mass-weighted whole-plane GFF sampling description with insertion −γ log|x−z| + γ log max(|x|,1), modulo constants. The unit-disc, γ ∈ (0,2), zero-integral-observation candidate in `/home/nitro/paper-fleets/hb/INPUT-REQUESTS.md:58` has the correct insertion and is consistent with its marked sampling argument. The source does not directly state that exact Lean equality for arbitrary carriers, circle-average versions, and measurable kernels: the marked cylinder identity and approximation/limit match still require verification. The unnormalized mass-biased bind is not the conditional normalized-root law; positivity and finiteness yield domination, not equality. DMS does not provide an Ω-valued measurable shift or domination on arbitrary extra Ω coordinates, and does not imply the global `hroot`.

The paper compares restrictions near z away from 0, retaining the smooth local term −α₀ log|x| and tracking additive normalization. The local projective-measure formulation in `LocalRootedComparisonRepair.md` is a candidate repair, not a proved replacement or a checked literature input. No downstream theorem is claimed closed by this verdict.

## Round c: consumer verdicts and remaining obligations

### 3′. DMS rooted interface: MINIMAL-CORRECTION (conditional)

The source-level interface is a marked, **observed field** statement, not an ambient-Ω shift: with `B = B₁(0)`, `H` the circle-average-normalized whole-plane GFF, and `λ = μ_H`, the unnormalized law of `(H mod constants, z)` weighted by `λ(dz)` on B is described by Lebesgue z and the field `H − γ log|·−z| + γ log max(|·|,1)` modulo constants. DMS21 Lemma A.10, whole-plane paragraph, PDF p. 184, explicitly gives the field sampling description; the marked cylinder identity and its realization with this repository's approximations remain to be checked, not postulated as an already verified Lean equality. Reweighting by `1/λ(B)` changes the joint law but preserves its null sets when `0 < λ(B) < ∞`. For `h = H − α₀ log|·|`, retain the additional `−α₀ log|·|` on the inserted side. DMS alone does not supply a local GMC decoder or the comparison of the actual measures.

The precise *sufficient replacement*, not asserted as a sourced theorem, is the observable domination in `docs/campaign/audits/LocalRootedComparisonRepair.md:13`: for `D j = {z : 3 r j < |z| ∧ |z| < 1 − 3 r j}`, `r j = 1/(16j)` for positive j, `κ = λ|B/λ(B)`, and the actual normalized, recentered restrictions `O j` and `V j` defined there,

```lean
Measure.map (O j) ((P ⊗ₘ κ).restrict (Prod.snd ⁻¹' D j)) ≪
  Measure.map (V j) ((volume.restrict (D j)).prod P)
```

This Lean-shaped type requires explicit measurable versions, a genuine measurable kernel and positive finite normalization. It must be paired with measurable local frequency predicates and the reference a.e. frequency statement for the **translated lattice phase**, with matching constants. DMS A.10 itself proves neither this type nor those extra premises. `RootedJointObservedFrequency.lean:19` and `RootedUniformPhaseCertificate.lean:23` are conditional infrastructure, not their discharge.

* **Lemma 8.2:** the paper's local transfer works conditional on the displayed domination, measurability and phase-sensitive reference frequency, since only the eventual tail event is transferred and finitely many initial scales are irrelevant. As currently formalized, `TypicalPointLiteratureAssembly.lean:24` calls `typicalPointManyGoodScalesStmt_of_ambientLaw` with the false global hypothesis, so replacing its hypothesis alone does **not** typecheck or prove the lemma; a local consumer must be built and the stated bridges proved. No source-level disproof of the numbered lemma is established.
* **Proposition 8.1:** `BoundaryTimeLiteratureAssembly.lean` uses Lemma 8.2 as a whole through `clusterBoundary_and_timeContinuity_of_literature`; it does not consume `hcomparison` independently. Once the same frozen `TypicalPointManyGoodScalesStmt` is actually proved, its downstream application needs no global law. The local comparison alone is insufficient to close it.
* **Proposition 7.2:** the same Section 7 assembly produces `ClusterTimeContinuityStmt` in the same conjunction and likewise has no independent rooted-law use. The other explicit Section 7 hypotheses remain required. This is a dependency audit, not a completed proof of either proposition.

### 1. E18 / Lemma 11.13: OPEN, not a false-result verdict

The requested four-way classification cannot honestly be resolved on the present evidence: neither positivity nor a counterexample is known here. The printed construction needs correction/justification, but its gaps do not establish a minimal correction to the **statement**, and `pinchPointEventWithInternalBounds` is a stronger auxiliary event, not the printed event. Exact evidence and quantifiers are in `docs/campaign/audits/E18PinchSourceCheck.md:8`. In particular the E₁ paths may leave B₆, the common buffered product gap is not established, the third contraction ratio is reversed, and the use of dyadic-square Lemma 11.10 for U,V is not immediate. The frozen statement's arbitrary ξ also exceeds the cited physical-ξ premise unless the axioms enforce it.

An exact sufficient missing Lean proposition is `hA` in `HarmonicBalls/Proofs/Sec11/BufferedPinchCanonicalLaw.lean:35`: for the same fixed proof configuration and each admissible parameter set and M, find `0 < b`, `0 < q ≤ 1` such that the displayed intersection has `0 < P {ω | ...}`. Its conjunction is E₁, E₂(M), the B₆ exit lower bound, `L < q*b`, and `q*C < H`; its exact binder types and formula are the cited declaration, not a claim of a published input. In addition the cited theorem requires its precise `hshiftLaw` and `0 < ξ` hypotheses. Neither the ordinary α₀ = 0 case nor general α₀ < Q (including γ) settles this joint proposition, and an alternative proof of the original numbered statement could avoid this sufficient strengthening. The actual research question is whether this joint proposition, or a different route to the frozen conclusion, follows from the specified metric-field assumptions; no new literature input is staged.

### 2. Lemma 11.8 cone representation: OPEN formal bridge; printed locality not refuted

The assertion at corrected TeX 2792–2796 that the cone event is local to the annulus is consistent with the displayed mass/Green definition and scaling, but the repository does not yet prove the needed joint measurable representation. `FixedShiftCircleLQGRepresentation.lean` supplies a common decoder for the two *actual* limits conditional on the two limit laws, buffered monotone exhaustion, continuity-set hypotheses and positive finite normalizing mass; it does not by itself encode the cone/Green event or discharge these premises. Thus neither FINE-AS-PRINTED nor CITED is established for the full Lean obligation, and no counterexample or necessary correction has been found.

The exact missing representation is: find countable `ι`, buffered measurable `A : ι → Set ℂ` and measurable `C : Set (ι → ℝ)` so that, for each of the original and fixed-smooth-shift actual measures η, almost surely

```lean
coneMassEvent η Q M r z ↔
  (fun i => (normalizedRestriction η U (A i)).toReal) ∈ C
```

Here U must contain the cone and Green-potential supports and the normalization is positive and finite; the actual quantifier and approximation conditions are those of `IsWholePlaneGFF.exists_fixedShift_normalizedMass_decoder` and `fixedShift_event_representation_with_insertion`. One must construct the Green supremum's countable measurable encoding, prove the two continuity-set and exhaustion hypotheses for the chosen sets, and then obtain `hE` and `hEp` in `ConeBadEventTransfer.lean:55`. This is a concrete unproved formalization obligation, not yet evidence of an open mathematical research problem. Separately the positivity, bump inclusion, parameter uniformity and frequency argument remain to be proved; the decoder alone does not prove Lemma 11.8.

## Resume verdicts (supersede the earlier cone-representation paragraph)

* **3′, local rooted interface — MINIMAL-CORRECTION, conditional:** the actual
  replacement is the marked projective-measure domination displayed in §3′
  above, with actual maps and measurable versions as specified in
  `audits/LocalRootedComparisonRepair.md`. DMS A.10 directly describes the
  mass-biased *field modulo constants* with the marked insertion, not that
  measure-level domination. The equality for this implementation's marked
  fields/GMC and the local decoder are not yet source-matched. For Lemma 8.2
  that domination suffices only together with measurable good events and the
  phase-sensitive reference frequency with matching constants. Props 8.1 and
  7.2 consume the resulting complete Lemma 8.2 and retain their other stated
  hypotheses; neither consumes the old global comparison independently.
* **E18 — OPEN RESEARCH QUESTION:** the printed argument needs repairs, but
  neither the frozen conclusion nor the stronger joint buffered positivity is
  proved false. The exact sufficient, not necessary, mathematical proposition
  is `hA` in `Proofs/Sec11/BufferedPinchCanonicalLaw.lean:35–44`, with one
  configuration fixed before field parameters and M. Its joint product gap,
  singular-origin and arbitrary-ξ scope remain unresolved as detailed above.
  No source justifies classifying the numbered statement itself as FALSE or
  prescribing a minimal statement correction.
* **11.8 cone-event representation — CITED as Lean infrastructure, with
  explicit premises:** `exists_coneMassEvent_countable_encoding` and
  `IsWholePlaneGFF.exists_enclosing_fixedShift_coneMassEvent_representation`
  (`Proofs/GFF/ConeMassLocalRepresentation.lean:155,334`, commit 8a4549f)
  prove the countable Green/cone encoding and a shared pairing-event decoder
  for the two actual limits, given the displayed cone measurability and
  enclosure, a smooth fixed shift, and original full support. The latter is
  available conditionally as `Section6.ae_fullSupport_all_singular_limits`
  (`Proofs/Sec6/SimultaneousSingularMeasure.lean:155`), using staged measure
  existence and the scaled-ball mass input; matching those sources and the
  actual limits in the consumer remains. Thus the earlier claim that this
  encoding and common continuity/exhaustion system were missing is superseded.
  This verdict addresses the representation, not an unconditional proof of
  the numbered 11.8 probability bound.

For the **printed 11.8 proof**, the bump and Weyl estimates need the following
explicit corrections; neither establishes a false numbered statement. First,
choose `C₁ > 0` small enough that `C₁ ≤ M C₂` before requiring the prescribed
bump to be nonnegative (or take its height to be the positive part of the
printed logarithm). Second, the factor called universal in the second step
cannot be taken independent of arbitrary α₀ and γ by the displayed Weyl
comparison. With `a = α₀ * γ`, if the entire annulus A_{r,6r}(z) is at
positive distance at least `r/100` from 0, then every point of it has modulus
between `r/100` and `7r`: the upper bound follows because the gap forces
`|z| < r` or `|z| > 6r`, but the latter case requires using `|z| + 6r` instead
of `7r`. In both cases a safe bound on the ratio of the largest and smallest
moduli is 1201: when `|z| < r`, use `7r/(r/100)`; when `|z| > 6r`, use
`(|z|+6r)/(|z|−6r) ≤ 1201`. Hence the Weyl weight ratio is at least
`1201^(-|a|)`, uniform in z and r for each fixed α₀, γ. In particular p may
be chosen after those parameters as in the frozen Lean statement; this
calculation does not justify a bound uniform over unbounded α₀. The ratio
argument additionally needs the actual Green functional's positive finite
values and Weyl monotonicity. The remaining Lean work is positive G, bump
inclusion, actual-limit/full-support source matching, and affine
translation/dilation uniformity, not the countable encoding. See
`audits/ConeFrequencySourcePlan.md` for the separate 11.8 → 11.7 argument.


## Operator no-further-prover policy, 2026-11-08 18:55 UTC (lead applied 19:13 UTC)

The operator's instruction in fleet inbox.md ends further written-proof requests. Formalize existing audited written proofs only. Any WRITTEN-PROOF-NEEDED implication with no audited proof remains its exact named Step hypothesis, with its location, type, consumer and reason recorded here and in PROGRESS. No worker is assigned to invent that proof. The three IDLA prover requests currently running are unavailable until independently audited. Historical requests above are evidence, not authorization to start another prover round.

E56 remains an interface obstruction, not a new background input or an uncovered proof assignment. The exact existing named hypothesis is `RawToProfileStep P gamma hC hcirc c`, defined at `HarmonicBalls/Proofs/Sec11/ClosureScales/PalmStepM.lean:42`:

```lean
def RawToProfileStep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (c : Ω → CanonicalProfile) : Prop :=
  IsWholePlaneGFF P hC hcirc → (∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2) →
    ∃ ρ : ((ℂ → ℝ) → ℝ) → CanonicalProfile,
      Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ] ρ ∧
      (∀ᵐ ω ∂P, ρ (hC ω) = c ω) ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        ∀ᵐ ω ∂P, ρ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) = shiftedProfile γ z (c ω)
```

It is consumed as `hB` by `palm_omega_of_stepM_stepB` in that file:61 and by `eq_r6_palm_lambda_of_stepM_stepB` in `PalmLambdaMeasurable.lean:94`. Its current full-function conclusion observes arbitrary nonpositive-radius values that its premise does not constrain. The independent-fair-bit counterexample is recorded with evidence in fleet ESCALATIONS.md E56:876. The operator must rule on carrier/restriction and the coded-Palm consumer; no worker is assigned to prove this false universal helper or change frozen files. The source's actual C(J,Real) construction has an audited proof in r10 lines927-950 and1257-1392, so its faithful prerequisites remain eligible work.

Checked at326a1ae: CountableCircleDecoder4202e55 and BorelCircleLimitDecoder326a1ae prove the continuous-code inverse and measurable countable-test-limit decoder on C(J,Real). MollifiedLogCircleLimitd95497e proves the deterministic logarithmic insertion limit for every insertion point. These do not discharge hB. The next two bounded Lean tasks follow the existing audited r10 lines1287-1330: continuous-addition limit and one-circle Gaussian L2 convergence. StepM is separately derived by PalmStepMDMS.lean:32 from explicit staged DMS hU, whose operator source review remains pending. H^-2 reconstruction/raw identification and all metric/rooted/numbered assembly obligations stay open.


## Superseding operator policy, 2026-11-09 00:55 UTC

The operator withdrew the18:55 no-further-prover rule. `MATH-OPEN-20261109.md` inventories the remaining mathematical requests, exact declarations/consumers, printed sources and refuted forms. One Codex prover, then independent Sol xhigh audit, then Lean. Its LEAN-PENDING list separates audited written arguments from new proof requests; in particular the local8.2 route and Section11 r10 repairs must not be mistaken for missing written mathematics. Existing source review and frozen/carrier decisions remain operator-owned.


## Operator rulings applied, 2026-11-09 03:00 UTC

This update supersedes earlier pending-ruling labels. E51 item 2 is written-proof closed for the actual bounded cluster/ball consumers by independently audited mcrt steps3 section 1:230-315 (sha256 d34cf930706e195c09ec2eb14c8999a6a1d64cc6b69938b6e227d2ddf9619d9d). The bounded Jensen premise yields source-potential integrability and exceptional-set control under the observation measure, followed by a bounded witness preserving pole and observation-a.e. values. Exact consumer references and the remaining Lean smooth-test/Fatou/localization steps are in MATH-OPEN-20261109.md item 2. The unrestricted full-plane assertion remains refuted.

E56: the operator explicitly authorizes the audited r10 actual C(J)/coded-Palm route for PalmStepM.lean's Omega consumer (hB:61) and PalmLambdaMeasurable.lean's lambda consumer (hB:94). Preserve RawToProfileStep's declaration and retire it from those consumers; do not prove it. The runner-promoted independent smooth-rate task remains active, and the actual-circle consumer repair is queued for z3. Existing deterministic measurable decoder and common-event GFF/DMS compatibility are proved; the consumer repair itself remains Lean-pending. No frozen declaration may change. DMS A.10 and other queued source matches remain explicit until operator review. Item 8 remains awaiting Ahmed's author-reading answer.

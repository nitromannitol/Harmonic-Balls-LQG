# Conditional Section 6 exports: bounded audit (2026-11-05)

**Verdict:** the four checked exports are Lean proofs of the *exact frozen
propositions conditional on I2 and zero-strength existence*. They are not
unconditional proofs, source approvals, or numbered-result closures. The
corrected-source identity problem E49 and the staged existence source check
remain open. The recursive semantic and source audits of the supporting
probabilistic, potential-theoretic, and field definitions are not completed by
this report. Hence this is not a passing full `lean-statement-audit` seal.

## Identity and source

`docs/campaign/FROZEN.md:50-55` pins the four proposition definitions in
`HarmonicBalls/Draft/Section6.lean`; that file and `Draft/Section2.lean` have no
changes relative to freeze commit `bd58fe6` (`git diff --stat bd58fe6 -- ...`).
The provider is `HarmonicBalls/Proofs/Sec6/SevenAdicFineSupportPrevalence.lean`.
The FROZEN inventory does not supply per-declaration hashes, versions or exact
provider pins; no stronger manifest identity is claimed. At this audit both TeX files have SHA-256
`8fdbb03043011800560e4d947eb79a3cfdd7cc8767a3af94469f04201b7593fc`.
They are byte-identical, so `paper/lqg_harmonic_ball-corrected.tex` does not
itself implement the corrections. E49 at `~/paper-fleets/hb/ESCALATIONS.md:345`
already reports this. E24 and the 2026-11-03 04:35 operator inbox adopt C23;
`~/paper-fleets/hb/CORRECTIONS-PROPOSED.md:72` specifies its reversal of the
exit-time event. E31 (inbox 04:45) orders constants before `α₀`. C1 governs I2.

| Frozen proposition | Frozen line | Conditional export (all names in `HarmonicBalls.Section6`) | Source |
|---|---:|---|---|
| `HarmonicBalls.HarnackTypeEstimateStmt` | 206 | `harnackTypeEstimateStmt_of_volumeGrowth_zero_existence` :120 | TeX 1065–1073 |
| `HarmonicBalls.HarnackTypeComponentStmt` | 230 | `harnackTypeComponentStmt_of_volumeGrowth_zero_existence` :109 | TeX 1078–1081, 1065–1073 |
| `HarmonicBalls.ManyGoodAnnuliStmt` | 255 | `manyGoodAnnuliStmt_of_volumeGrowth_zero_existence` :87 | TeX 1169–1174 |
| `HarmonicBalls.ManyVeryGoodAnnuliStmt` | 311 | `manyVeryGoodAnnuliStmt_of_volumeGrowth_zero_existence` :98 | TeX 1296–1301; definitions 1125–1157 |

The frozen declarations are `def ... : Prop`, not theorem exports or sorry
bodies. Their contents, rather than just their names, are compared below.

## Premises and consumption

Each provider has exactly these two proposition-valued inputs, at the same
universe `u` as its conclusion:

1. `hgrowth : HarmonicBalls.LQGVolumeGrowthAllScalesStmt.{u}` (I2;
   `Draft/Section2.lean:122`). This is a **derived numbered-input assumption**,
   not part of the four source conclusions and not a staged literature axiom.
   It quantifies `γ α₀`, the probability space and field, then one a.s. event,
   on which all positive `R` and admissible `βplus, βminus` have an `r₀ > 0`
   giving both ball-mass bounds for all `0 < r < r₀` and `z ∈ B_R`. The
   admissible bounds explicitly include `γ * (Q - α₀)`. C1 and C2 apply.
2. `hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
   (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
   LQGMeasureExistence P γ 0 hC hcirc`. Expanding
   `Proposed/LQG.lean:64`, each instance asserts
   `IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
   ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ`.
   This is staged and awaiting operator source-check. The proposed declaration
   cites Duplantier–Sheffield 2011 Prop. 1.1 p. 5 (bounded zero-boundary case;
   whole-plane extension is a further claim) and Berestycki–Powell 2024 v2
   Thm. 2.1 p. 62; neither the whole-plane transfer nor the exact a.s. dyadic
   limit on arbitrary realization spaces is approved by this audit.

Both are **EXCESS** as hypotheses of each unconditioned numbered result; they
are made explicit, not hidden in a conclusion-shaped hypothesis. The typed
examples in `HarmonicBalls/Audit/Section6ConditionalExports.lean` use I2 and
the fully expanded E0 to produce each frozen proposition. They apply each
actual provider directly. The existence premise is used in
`Prevalence.lean:93-106,122-136` to obtain a zero-strength measure in the same
space; the event transfer subsequently uses the proved Weyl scaling theorem
`LQGWeylScaling.lean:121`, not a Weyl-scaling premise of the exports. Affine
invariance is supplied by `Proofs/Sec9/AffineInvarianceAssembly.lean:18`, not
an extra assumption. These composition witnesses do not prove either premise.

## Frozen binder and carrier review

The following is a compact binder-by-binder classification, shared where the
four definitions have the identical binder. Counts refer to binder *groups*
listed in this table, not Lean's individual elaborated metavariables. SOURCE
includes quantifiers read from the source and standing field setup; TYPING is
the explicit Lean carrier; RULED is an operator-adopted reading; EXCESS is a
condition absent from the source conclusion. Provider premises are counted
separately above.

| Binder group | Applicable statements | Bin | Evidence / scope |
|---|---|---|---|
| `∃ c > 0` | all | SOURCE | universal c first, TeX 1069, 1171, 1297 |
| `∃ C₃ > 0` | 6.6 | SOURCE | universal, before γ, TeX 1297 |
| `∀ γ, 0 < γ < 2` | all | SOURCE | standing subcritical LQG setup |
| `∀ βminus > (2+γ)^2/2` | 6.6 | RULED / **scope unresolved** | parameter of M, TeX 1126–1129; draft 304–310; see below |
| `∀ b ∈ (0,1)` | 6.3, 6.6 | SOURCE | TeX 1170, 1297 |
| `∃ a ∈ (0,1)` | 6.3, 6.6 | SOURCE | definition TeX 1115–1117; draft 250–254 states monotonicity reading |
| `∃ C₁m,C₁p,C₂m,C₂p > 0` | 6.6 | SOURCE | TeX 1297 and 1145–1150 |
| `∃ N₁ ≥ 1; ∀ N₀ ≥ N₁` | 6.6 | SOURCE | TeX 1297–1298 |
| `∃ α > 0` | 6.1, 6.2 | SOURCE | TeX 1066; shared setting at 1079 |
| `∀ α₀ < Q` after constants | all | RULED | E31, inbox 04:45; source setup |
| `∀ Ω [MeasurableSpace Ω] P hC hcirc μ` | all | TYPING | `μ : Ω → Measure ℂ`, field observables over ℂ; arbitrary realization |
| `IsWholePlaneGFF P hC hcirc` | all | SOURCE | standing GFF; structure fields in `Defs/GFF.lean:93-109` |
| `IsLQGMeasureOfField P γ α₀ hcirc μ` | all | SOURCE | standing LQG measure; `Defs/LQG.lean:48-74` |
| `∃ E : ℝ → ℂ → Set Ω` | 6.1, 6.2 | SOURCE | TeX 1066–1073 and 1078–1081 |
| `∀ ω, ρ ∈ (0,1), x₀, z ∈ B₁, t > 0`, event and containment premises | 6.1, 6.2 | SOURCE | TeX 1066–1067; draft 199–205 explains t and pointwise event readings |
| `∀ Λ ∈ connectedComponentsIn (cluster ∩ ball)` | 6.2 | SOURCE | TeX 1079–1080 |
| `PolyHighProb` and grid/radii tests | all | SOURCE | TeX statements; expanded below |
| Additional I2 and E0 premises | frozen statements | none | appear only in conditional providers, not in frozen declarations |

Counts per statement (by table groups): 6.1 = SOURCE 7, RULED 1, TYPING 1,
EXCESS 0; 6.2 = SOURCE 8, RULED 1, TYPING 1, EXCESS 0; 6.3 = SOURCE 7,
RULED 1, TYPING 1, EXCESS 0; 6.6 = SOURCE 10, RULED/scope unresolved 1,
RULED 1, TYPING 1, EXCESS 0. These are a bounded surface review, not a
recursive approval of every assumption or definition.

**6.6 quantifier question:** the paper specifies `a = a(b,γ)`, `N₁ =
N₁(b,γ)`, and `C₁±, C₂±` depending on `a,γ` (TeX 1297). The frozen Lean
statement universally chooses `βminus` *before* `a`, the C's, and N₁ (draft
311–321). It therefore permits these witnesses to depend on `βminus`. Draft
304–310 explains the reading that the paper's exponent is chosen through γ,
but the cited source does not explicitly say that arbitrary β-dependent
witnesses meet the printed dependencies. This is a source-scope discrepancy /
interpretation requiring an operator ruling, not a claim that the result is
false. E31 explicitly resolves the order relative to α₀, not this β question.

`PolyHighProb` (`Defs/Notation.lean:27`) uses a real positive exponent and
bounds outer probability of the complement; this allows nonmeasurable events.
`prevalenceGrid` (`Draft/Section6.lean:139`) is exactly the printed punctured
lattice. In 6.3 and 6.6 the scales are respectively `7⁻ⁿ` and `8⁻ⁿ` in
`[ε, sqrt ε]`, and the logarithms have corresponding bases; 6.1–6.2 use the
natural logarithm. The 6.1 conclusion uses an open half-ball; 6.2 uses a
closed half-ball. 6.2 restates the 6.1 prevalence in the same event family,
as an interpretation of its reference to the 6.1 setting.

`IsGoodAnnulus` (`Defs/Annuli.lean:47`) quantifies Borel `Y`, annular mass and
all starts on the `4r` sphere, with the C23-reversed exit-time comparison.
This differs from the literal TeX 1119–1121 but follows the adopted correction.
`IsVeryGoodAnnulus` (`Defs/Annuli.lean:81`) contains all three VG clauses,
uses ENNReal ratios and the unshifted scaled lattice. The ENNReal zero-denominator
conventions and the diagonal value in `annulusGreenPotentialSup` (line 65)
require a separate detailed semantic audit; neither follows merely from the
provider examples. `IsLQGMeasureOfField` expands to an a.s. locally finite
dyadic vague limit; `IsWholePlaneGFF` bundles measurability, joint Gaussianity,
centering, covariance and a.s. circle-average continuity. The semantic match
of these shared foundations is not certified here.

## Actual dependency path and circularity

* 6.3 provider → `manyGoodAnnuliStmt_of_literature` (`Prevalence.lean:153`)
  → `manyGoodAnnuliStmt_of_subRange` and `singularWeightStep_of_weyl`; its
  subrange premise is supplied by
  `goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport` (provider :74).
  This goes through `sevenAdic_goodAnnulus_probability_of_volumeGrowth`
  (:20) → `ae_uniform_goodAnnulus_threshold_on_dyadic_phases`
  (`UniformGoodAnnulusFineSupport.lean:251`) →
  `ae_ae_lqg_fine_support_of_disc_dyadic` (`DiscDyadicRecurrence.lean:99`)
  using I2 and proved affine invariance. The probability-to-prevalence step
  is `goodAnnuliSubRangeStep_of_sevenAdic_reference_probability`
  (`SevenAdicProbabilityReduction.lean:48`) and explicitly uses fine-support,
  field-measurability, Brownian point avoidance, recentering, and the fixed-centre
  geometric annulus iteration (`PrevalenceGridUnion.lean:64`).
* 6.6 provider → `manyVeryGoodAnnuliStmt_of_literature`
  (`Prevalence.lean:162`) → `manyVeryGoodAnnuliStmt_of_subRange` and the same
  zero-strength/Weyl comparison. Its very-good subrange is derived from the
  good subrange and I2 by `veryGoodAnnuliSubRangeStep_of_goodPrevalence`
  (`AffineInvarianceAssembly.lean:30`) →
  `veryGoodAnnuliSubRangeStep_of_goodPrevalence_of_translation`
  (`DyadicVeryGoodPrevalence.lean:86`).
* 6.2 provider → `harnackTypeComponentStmt_of_goodPrevalence_of_translation`
  (`DyadicVeryGoodPrevalence.lean:131`) →
  `harnackTypeComponentStmt_of_volumeGrowth_and_prevalence`
  (`VolumeGrowthConsequences.lean:26`) →
  `harnackTypeComponentStmt_of_harmonicMeasure` and `_of_volumeGrowth`
  (`VolumeGrowthAssembly.lean:59,45`) → `harnackTypeComponentStmt_of_steps`
  (`Assembly.lean:132`) → `harnackTypeComponentStmt_of_lemmas`
  (`HarnackType.lean:58`), using the **derived** 6.6 and 6.11 results.
  I2 supplies 3.2, the 6.8/6.10 odometer estimates, and the 6.9 Brownian
  comparison (`PlanarBrownianGenerator.lean:60`); the decay and component
  maximum steps finish the 6.11 chain (`VolumeGrowthAssembly.lean:20-36`).
* 6.1 follows the analogous route (`DyadicVeryGoodPrevalence.lean:146`,
  `VolumeGrowthConsequences.lean:38`, `VolumeGrowthAssembly.lean:70`) and
  applies `harnackTypeEstimateStmt_of_component` (`HarnackType.lean:33`) to
  the derived 6.2. Use of 6.6 by 6.2 and 6.2 by 6.1 is forward composition,
  not an assumption of those propositions at the top-level provider.

The annulus iteration reaches `annulusIterationStmt_proved`
(`AnnulusLawTransfer.lean:207`), the Leonardo Bonanno implementation
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, and the field-law bridge
modules `LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`, `.CircleAvgRate`, and
`.ExistGFF` (see `SevenAdicProbabilityReduction.lean:4-11`).

A transient Lean environment traversal recursively followed **values** of
project-prefixed constants from each provider (1184, 1393, 1785, 1788 names,
respectively). The only four audited top-level provider names reached were
the respective roots. The traversal also found the expected *other* proof
producers for 6.6 and 6.2 as described above, and no project I2 producer named
`lqgVolumeGrowthAllScalesStmt_of...` in these closures. Thus no feedback is
seen through that named path: I2 is supplied as a variable. This value-only,
project-namespace traversal is a reproducible bounded check, not a complete
semantic audit of all imported non-project constants or of arbitrary alternative
producers of I2. A separate value traversal from the I2 producer `lqgVolumeGrowthAllScalesStmt_of_literature` (`Proofs/Sec2/Assembly.lean:120`) and its `_of_DG` helper reached 177 and 166 project constants respectively, and neither reached any of the four named providers or their flagged target producers. The traversals follow `ConstantInfo.value? (allowOpaque := true)` and `Expr.getUsedConstantsAsSet`, recursively keeping names with the `HarmonicBalls.` prefix. I2 source review remains pending.

## Verification and limitations

`~/paper-fleets/hb/lc HarmonicBalls/Audit/Section6ConditionalExports.lean` and
`~/paper-fleets/hb/lb HarmonicBalls.Audit.Section6ConditionalExports` pass.
For **each** of the four providers `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`; this checks axiomatic closure, not
hypotheses or fidelity. The audit file contains no proof placeholders. The
above conditional Lean result does not close any numbered theorem or approve
I2's derivation, staged LQG existence, E49's source reconciliation, the β
quantifier interpretation, or the deep dependency-chain semantic audit.

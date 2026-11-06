# Section 10 Jordan export audit

Verdict: **conditional, not a closure of Proposition 10.7**. The audited
`harmonicBallComplementBoundaryJordan_of_proved_scaling` has the frozen
conclusion but assumes Theorem 5.5 existence and Proposition 10.6. No source
admission is made here. The companion Lean consumer checks the explicit
conclusion and substitutes proved ingredients; a second route avoids general
coordinate change.

## Identity and source

Audit baseline `0b292aa4297cd90cb8355b541394e1acad23201c`; frozen
`Draft/Section10.lean:116`, SHA-256
`275309fd7bddd433689c4c10ec2034f7f81ec7d54c84fdb562e6d9b7a03db481`;
`FROZEN.md:75–76`. Primary source `paper/lqg_harmonic_ball-corrected.tex`,
SHA-256 `8fdbb03043011800560e4d947eb79a3cfdd7cc8767a3cf94469f04201b7593fc`,
10.6 at 2622–2681 and 10.7 at
2684–2691. The latter cites 5.7, 10.1, a union bound and 5.5; the actual
transfer uses 10.6 implicitly. The current corrected TeX still prints the
uncorrected 10.6 `B₁` complement: adopted C16/E17 supplies the plane
complement in the frozen statement. `Proofs/Counterexamples/Prop10_6.lean`
certifies the printed issue; the source discrepancy is already escalated in
fleet `ESCALATIONS.md` (E17 and source-artifact discrepancy).

## Binders and witnesses

| Scope | Exact content |
| --- | --- |
| Outer parameters | For every `γ, α₀ : ℝ` with `0 < γ < 2`, `α₀ < lqgQ γ`, and every `Ω : Type u` with measurable space, measure `P`, pairings `hC`, circle averages `hcirc`, and random measures `μ`, assume `IsWholePlaneGFF P hC hcirc` and `IsLQGMeasureOfField P γ α₀ hcirc μ`. |
| Input family | **Every** `Λ : Ω → ℂ → ℝ → Set ℂ` with `∀ᵐ ω ∂P, ∀ z, IsHarmonicBallFamily (μ ω) (Λ ω z) z`. Its event may depend on `Λ`. No joint measurability of `Λ` is required. |
| Output | An event depending on the outer parameters and `Λ`, on which **all** positive `t`, all `z : ℂ`, and all `C ∈ connectedComponentsIn (closure (Λ ω z t))ᶜ` satisfy `IsSimpleLoop (frontier C)`. Complement and frontier are in `ℂ`; the unbounded component is included. |
| Loop witness | `IsSimpleLoop` means `∃ φ : Circle → ℂ, Continuous φ ∧ Function.Injective φ ∧ Set.range φ = frontier C` (`Defs/Geometry.lean:105`). The witness may depend on ω, t, z, C. |
| Existence premise | For each model there is one almost-sure event on which `∀ z, ∃ A : ℝ → Set ℂ, IsRegularizedClusterFamily (μ ω) A z` (`Draft/Section5.lean:192`). The chosen family may depend on ω and z. `JordanIntegerRadii.lean:104` uses classical choice to build `Λhat` for every ω,z; the conditional definition gives no joint measurability claim. |
| 10.6 premise | For each model one event works for all `t > 0`, `z ∈ B₁` with compact containment, and all plane-complement components, with a separate loop witness for each. |
| I2 premise | One event works for every `R > 0` and allowed pair of exponents; `r₀ > 0` may depend on ω, R and the exponents and controls all `0 < r < r₀` and all `z ∈ B_R` (`Draft/Section2.lean:122`). |

The original export (`Proofs/Sec10/ScalingAssembly.lean:34`) has five
universal premises: I2, existence, 10.6, affine invariance and coordinate
change. The affine premise quantifies over all Ω, P, hC, hcirc; the
coordinate-change premise additionally quantifies over *all* γ and α₀.
Its definition (`Proposed/LQG.lean:108`) supplies an event for each model
and μ on which all nonzero complex `a` and all `b` work. These assumptions
are Props, not kernel axioms.

## Proof chain and replacements

`auditJordanExport` expands the exact target and uses the original export;
`wholePlaneGFFAffineInvariance_proved` (`Proofs/Sec9/AffineInvarianceAssembly.lean:18`)
replaces its staged affine premise. `clusterPathwiseScaleStep_proved`
(`Proofs/Sec5/SupersolutionScaling.lean:153`) already replaces the pathwise
scaling step. `JordanScaling.lean:82` transports the one-event unit-disc
result to a fixed radius, and `JordanIntegerRadii.lean:46` intersects the
countably many events. At `JordanIntegerRadii.lean:61`, boundedness and
regularized-cluster compatibility select an integer radius after ω,t,z;
openness gives equality of closures. I2 supplies openness, full support and
the uniqueness assembly, so the chosen regularized family agrees with each
given harmonic-ball family on positive times. All these steps preserve the
simultaneous centre/time event.

The separate `auditJordanExport_dyadic` uses the existing
`harmonicBallComplementBoundaryJordan_of_dyadic`
(`Proofs/Sec10/JordanDyadicScaling.lean:76`), which derives dyadic measure
rescaling from the dyadic definition and field covariance and extends to a
fixed radius by cluster compatibility. It requires only I2, existence and
10.6, without the general coordinate-change hypothesis. This is an
alternative proved assembly, not a claim that the original export proved
its coordinate-change premise.

`auditJordanExport_of_staged` replaces I2 via
`lqgVolumeGrowthAllScalesStmt_of_existence`
(`Proofs/Sec9/ExistenceResultsAssembly.lean:36`). The exact remaining staged
universal inputs are `WholePlaneLQGBallMassBounds P γ hC hcirc`,
`LQGMeasureCoordChange P γ 0 hC hcirc`, and
`LQGMeasureExistence P γ α hC hcirc` for every α, each universally over
Ω, P and its remaining arguments. That assembly uses proved affine
invariance, `Section6.lqgMeasureWeylScaling`, and conditional
`Section6.lqgMeasureNonatomic_of_existence`; the latter relies on the
stated mass and all-strength existence inputs. These are staged in
`Proposed/LQG.lean`, pending operator source-check, and the Section 6 chain
awaits campaign audit. This is LQG measure existence, distinct from the
still-assumed harmonic-ball existence.

The available existence assembly (`Proofs/Sec5/ExistenceFromVolumeGrowth.lean:20`)
reduces Theorem 5.5 to I2, 5.3, 7.1, 7.2 and scaling inputs; it does not
discharge it here. No proof of 10.6 was located in the Section 10 proof
modules. The stronger route does not erase either premise.

## Bounded frontier for 10.6

The paper's steps require local connectivity and absence of cut points,
then a planar Jordan characterization. A bounded next task is to establish
the exact deterministic bridge from the available complementary-frontier
properties to `IsSimpleLoop`, supplying and proving the necessary planar
topology rather than staging an unsourced bridge. Existing conditional facts:
`ae_cluster_localConnectivity_and_frontier_of_zero_existence`
(`Proofs/Sec10/ExistenceLocalConnectivity.lean:22`),
`ae_cluster_frontier_has_two_complement_components`
(`FrontierTwoComponents.lean:72`), and
`ae_cluster_frontier_deletion_compl_connected`
(`FrontierDeletionConnectivity.lean:69`); all retain frozen Lemma 10.5.
Separately resolve 10.5 and derive the no-cut/Jordan bridge before assembling
10.6; do not infer no cut points from these facts without a proved theorem.

E41 is material: `CrossingImpliesNoHoles.lean:77` proves I2 plus the
frozen `CrossingComponentContainsClusterCrossingStmt` implies connected
complement for every compactly contained cluster closure. The deterministic
annulus counterexample to the general topological assertion is described
in fleet `ESCALATIONS.md:200`. This is not an LQG cluster counterexample;
whether the cluster hypotheses establish that no-hole consequence remains
open. It cannot be silently treated as an available topological lemma.

## Verification

`Audit/Section10JordanExport.lean` checks the original expanded consumer,
dyadic consumer and staged-I2 consumer. `#print axioms` for each reports
`[propext, Classical.choice, Quot.sound]`. Bonanno's Cameron–Martin port is
consumed through Lattice-Probability in the imported proof chain. No staged
input has been admitted or asserted unconditionally.

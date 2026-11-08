# Audit: BoundedDensityGreenContinuity (task green-bounded-density-interior-continuity, worker q2)

File: `HarmonicBalls/Proofs/Potential/BoundedDensityGreenContinuity.lean` (110 lines, new, namespace `HarmonicBalls`).
Scope: Lebesgue bounded densities and interior poles only. Not continuity for singular measures, not boundary
regularity, not the E51 closure, not a numbered result.

## Declarations (all proved; no hypothesis beyond the stated ones)

| line | declaration | conclusion |
|---|---|---|
| 33 | `integrable_greenFunction_mul_bdd` | for every pole `x : ℂ`, `Integrable (fun y => greenFunction U x y * f y)` |
| 44 | `abs_integral_greenFunction_mul_sub_le` | for all `x z : ℂ`, `abs ((∫ y, G x y * f y) - ∫ y, G z y * f y) ≤ M * ∫ y, abs (G x y - G z y)` |
| 76 | `continuousOn_integral_greenFunction_mul_bdd` | `ContinuousOn (fun x => ∫ y, greenFunction U x y * f y) U` |
| 99 | `greenPotential_boundedDensity_interior` | conjunction of the three, with `(_hM : 0 ≤ M)` |

`G x y` abbreviates `greenFunction U x y` (`Defs/Green.lean:70`: value `0` unless `x, y ∈ U` and `x ≠ y`).
Orientation: the pole is the first argument, the integration variable the second, as in the source lemma.

## Binders and carrier

- `U : Set ℂ`, `hU : IsOpen U`, `hUb : Bornology.IsBounded U`.
- `f : ℂ → ℝ`, `hf : AEStronglyMeasurable f volume`, where `volume` is the Lebesgue measure on `ℂ`.
- `M : ℝ`, `hfM : ∀ᵐ y ∂(volume : Measure ℂ), |f y| ≤ M`.
- Poles range over all of `ℂ`: `greenFunction U x = 0` off `U`, and `integrable_greenFunction_pole` holds for every `z : ℂ`.
- `(_hM : 0 ≤ M)` appears only in the packaged statement, as specified. It is unused in the proof, because the a.e.
  bound on the nonnull measure `volume` already forces `0 ≤ M`. The name carries the underscore to satisfy
  `-DwarningAsError=true` (the unused-variable linter rejected `hM` on the first check).
- No continuity, support, boundary or source-free hypothesis on `f`.

## Sources reused (no new analysis)

- `integrable_greenFunction_pole` : `HarmonicBalls/Proofs/Potential/GreenPoleL1Continuity.lean:62`
  (`Integrable (greenFunction U z)` for all `z`).
- `tendsto_integral_abs_greenFunction_sub_nhdsWithin` : `GreenPoleL1Continuity.lean:229`
  (`x ∈ U`: `Tendsto (fun z => ∫ y, |G z y - G x y|) (𝓝[U] x) (𝓝 0)`), from `tendsto_integral_abs_greenFunction_sub`
  at `GreenPoleL1Continuity.lean:194`.
- Mathlib (checked by name at the pinned Mathlib): `Integrable.mul_bdd` (`MeasureTheory/Function/L1Space/Integrable.lean:1073`,
  bounded factor with `∀ᵐ`-bound, `c` implicit), `integral_sub` (`Integral/Bochner/Basic.lean:263`),
  `norm_integral_le_integral_norm` (`Bochner/Basic.lean:967`), `integral_const_mul` (`Bochner/Basic.lean:290`),
  `integral_mono_of_nonneg`, `Integrable.abs`, `Integrable.const_mul`, `squeeze_zero'`,
  `tendsto_iff_dist_tendsto_zero` (`Topology/MetricSpace/Pseudo/Defs.lean:1199`), `Filter.Eventually.of_forall`
  (`Order/Filter/Basic.lean:663`).

Proof route. (1) `integrable_greenFunction_mul_bdd`: `Integrable.mul_bdd` with the row integrable and `f` bounded a.e.
(2) `abs_integral_greenFunction_mul_sub_le`: split the difference of integrals by `integral_sub`, bound
`|∫ (G x - G z) f| ≤ ∫ ‖(G x - G z) f‖ ≤ ∫ M |G x - G z|` by `integral_mono_of_nonneg` (a.e. `|f| ≤ M`),
then `integral_const_mul`. (3) `continuousOn_...`: for `x₀ ∈ U`, `dist (Φ z) (Φ x₀) ≤ M ∫|G z - G x₀|` for all `z`,
which tends to `0` along `𝓝[U] x₀` by the scalar input; squeeze.

## Existing providers searched first (none is an exact provider of the statement)

- `Defs/Green.lean:89` `greenPotential O μ x := ∫ y, greenFunction O x y ∂μ`: a definition for a measure `μ`, with
  no density form and no continuity statement.
- `Proofs/Potential/GreenPotentialHolder.lean:500`, `:529` (`greenPotential_ball_holderOnWith`,
  `greenPotentialBall_continuousOn`): Hölder (line 500, under volume-growth bounds on `μ`) and continuity (line 529,
  for locally finite `μ`) results for the ball Green potential `greenPotentialBall μ R`; they concern the ball Green
  function, not `greenFunction U` for general bounded `U`.
- `Proofs/Potential/TranslatedDiscSourceFreeHarmonicity.lean:54`, `:81`: continuity of `greenPotential (ball c R) ν`
  the `:81` statement needs a finite `ν` with `ν U = 0` (no mass on `U`), and `:54` a compact source set `K` with
  `ν Kᶜ = 0`; the potential there is `greenPotential` of a measure, source-free on `U`. Not reused.
- `Proofs/Potential/ObserverGreenLInfinityAdjoint.lean` (`bounded_observer_green_row`,
  `existsUnique_observer_green_Linfinity_operator`, `observer_green_Linfinity_duality`): carry an upper
  volume-growth hypothesis `hup` on `μ`; not reused.
- `Proofs/Potential/GreenReciprocalPairing.lean:17` `green_reciprocal_pairing`: for bounded densities `f, g` on a
  bounded open `V`, integrability of the kernel products and a reciprocal (Fubini-type) pairing identity; no
  continuity-in-pole conclusion; not reused.
- `Proofs/Potential/GreenRowL1Continuous` (commit b7d689b) is not imported, per the task.

## Checks

- `lc` (project options with `-DwarningAsError=true`): CHECK OK.
- `lb HarmonicBalls.Proofs.Potential.BoundedDensityGreenContinuity`: BUILD OK.
- Printed axioms (scratch file outside the repo, `/tmp/q2-bdg/AxCheck.lean`, checked by `lc`): all four declarations
  depend on `[propext, Classical.choice, Quot.sound]` only.
- Raw scan of the file for `sorry`, `axiom`, `admit`, `native_decide`, `maxHeartbeats`, `set_option`: 0 hits
  (so the comment-aware scan is clean as well).

## Import closure

- Direct import: `HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity` only.
- Closure (BFS over HarmonicBalls modules, this module included): 352 HarmonicBalls modules; 48 direct Mathlib
  imports; 12 direct external imports: 11 `MarkovProcess.*`, and `LatticeProb.Prob.Birkhoff` (the pinned
  Lattice-Probability lean-v4.35 port).

## Credit

The module docstring credits Leonardo Bonanno, reached through the pinned Lattice-Probability lean-v4.35 port
(module `LatticeProb.Prob.Birkhoff` in the import closure of `GreenPoleL1Continuity`). The new file itself adds no
other code of his.

## Consumers

- In the repository at this commit: none. A grep of the four declaration names over `HarmonicBalls/` finds no use
  outside this file.
- Wiring to any `Steps/` or `Draft/` consumer is not done here; that is the operator's routing.

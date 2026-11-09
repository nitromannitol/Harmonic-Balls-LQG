# Audit: GreenPotentialFunctionalContinuity (task green-pole-functional-norm-continuity, worker q2)

Module: `HarmonicBalls/Proofs/Potential/GreenPotentialFunctionalContinuity.lean` (new, 106 lines, namespace `HarmonicBalls`).
Carriers: `L∞` is `Lp ℝ ∞ (volume : Measure ℂ)`. The functionals live in `Lp ℝ ∞ volume →L[ℝ] ℝ` with its operator norm, so `ContinuousOn` and `UniformContinuousOn` are for the operator-norm topology. The Green row is `greenFunction U x : ℂ → ℝ` (`Defs/Green.lean`, value `0` off `U`).
Hypotheses of every declaration: `(hU : IsOpen U) (hUb : Bornology.IsBounded U)`, plus the pole data. No `External` or `Proposed` module, no literature input, no hypothesis on the norm, the continuity or a kernel operator.
`Φ x` abbreviates `greenPotentialLInfinityFunctional hU hUb x`. It is used as defined, with its representative formula `greenPotentialLInfinityFunctional_apply`; neither is redefined or changed.

## Declarations

| Line | Declaration | Statement (binders, abbreviated) |
|---|---|---|
| 45 | `norm_greenPotentialLInfinityFunctional_sub_le` | `(hU) (hUb) (x z : ℂ)`: `‖Φ x - Φ z‖ ≤ ∫ y, \|G_U(x,y) - G_U(z,y)\|` |
| 76 | `dist_greenPotentialLInfinityFunctional_le` | `(hU) (hUb) (x z : ℂ)`: `dist (Φ x) (Φ z) ≤ dist (greenRowL1 hU hUb x) (greenRowL1 hU hUb z)` |
| 85 | `continuousOn_greenPotentialLInfinityFunctional` | `(hU) (hUb)`: `ContinuousOn (fun x => Φ x) U` (operator norm) |
| 97 | `uniformContinuousOn_greenPotentialLInfinityFunctional` | `(hU) (hUb) {K : Set ℂ} (hKU : K ⊆ U) (hK : IsCompact K)`: `UniformContinuousOn (fun x => Φ x) K` (operator norm) |

## Route (formal packaging of the written argument; no new mathematics)

1. Norm (line 45). `ContinuousLinearMap.opNorm_le_bound` with bound `∫ |G_x - G_z|`. For a fixed `f`, `(Φ x - Φ z) f = ∫ (G_x - G_z) f` (`sub_apply`, `greenPotentialLInfinityFunctional_apply`, `sub_mul`, `integral_sub`). Then `|∫ g f| ≤ ∫ |g f|` (`abs_integral_le_integral_abs`), and `|f| ≤ ‖f‖` almost everywhere (`abs_coeFn_le_norm_ae_top`) gives `|g f| ≤ |g| ‖f‖` (`integral_mono_ae`, `integral_mul_const`).
2. Distance (line 76). `dist_greenRowL1` (the `L¹` distance of the rows is `∫ |G_x - G_z|`), `dist_eq_norm`, and (1).
3. Continuity (line 85). `tendsto_iff_dist_tendsto_zero` and `squeeze_zero'`, with `continuousOn_greenRowL1` (the pole continuity of the `L¹` row, from `GreenPoleL1Continuity`) and (2).
4. Uniform continuity (line 97). `Metric.uniformContinuousOn_iff`, with `uniformContinuousOn_greenRowL1` on `K ⊆ U` compact and (2).

## Providers (exact source)

- `HarmonicBalls/Proofs/Potential/GreenPotentialLInfinityFunctional.lean` (commit 9a95b7c): `abs_coeFn_le_norm_ae_top` :42; `integrable_greenFunction_mul_coeFn` :54 (`hU hUb x f`); `greenPotentialLInfinityFunctional` :101; `greenPotentialLInfinityFunctional_apply` :110 (the representative formula).
- `HarmonicBalls/Proofs/Potential/GreenRowL1Continuous.lean` (commit b7d689b): `greenRowL1` :37; `dist_greenRowL1` :69; `continuousOn_greenRowL1` :75; `uniformContinuousOn_greenRowL1` :83 (`hKU hK`).
- `HarmonicBalls/Proofs/Potential/GreenPoleL1Continuity.lean` (commit 7b9c811): `integrable_greenFunction_pole` :62; `integrable_abs_greenFunction_sub_pole` :75 (its arguments are `(z x)` and its integrand is `|G z - G x|`, so the call `… x z` gives `|G x - G z|`).
- Mathlib: `ContinuousLinearMap.opNorm_le_bound`; `sub_apply` (the `ContinuousLinearMap.sub_apply` name is deprecated); `integral_sub`; `integral_mono_ae`; `abs_integral_le_integral_abs`; `integral_mul_const`; `Integrable.abs`; `Integrable.mul_const`; `Integrable.congr` (`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:127`); `Metric.uniformContinuousOn_iff` (`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:762`); `tendsto_iff_dist_tendsto_zero` (`Pseudo/Defs.lean:1199`); `squeeze_zero'`; `dist_eq_norm`; `Real.norm_eq_abs`.
- Search before proving: a grep of HarmonicBalls for `greenPotentialLInfinityFunctional` and `opNorm_le_bound` finds them only in `GreenPotentialLInfinityFunctional.lean` (before this file). No existing operator-norm difference estimate or continuity lemma for these functionals is duplicated.

## Import closure

- Direct imports: `GreenPotentialLInfinityFunctional` (9a95b7c) and `GreenRowL1Continuous` (b7d689b). Neither imports `GreenRowUniformIntegrability.lean`.
- Lean closure (`#eval` on `env.header.moduleNames`, scratch `/tmp/q2-ax/Closure2.lean`, log `logs/lc/020552-1110179.log`): total 11,799; HarmonicBalls 355 (this module included); Mathlib 8,537; MarkovProcess 152; LatticeProb 2; forbidden `GreenRowUniformIntegrability` 0.
- Git closure over `HEAD` imports: 354 HarmonicBalls modules besides this one. Changed after 9a95b7c among them: 0.

## Checks

- `lc`: CHECK OK (`logs/lc/020329-855686.log`).
- `lb HarmonicBalls.Proofs.Potential.GreenPotentialFunctionalContinuity`: BUILD OK (`logs/lb/020425-945571.log`).
- Printed axioms (scratch file, `logs/lc/020543-1095370.log`): all four declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- Raw scan of the owned file for `sorry|axiom|admit|native_decide|maxHeartbeats|set_option`: 0 hits. Comment-aware scan (block and line comments removed first): 0 hits.
- Dev fix: the first `lc` run failed only on the deprecated `ContinuousLinearMap.sub_apply`, replaced by `sub_apply`.

## Credit

The module docstring credits Leonardo Bonanno. His code reaches this file only through the pinned Lattice-Probability (lean-v4.35) port (the `LatticeProb.Prob.*` modules in the import closure).

## Remaining consumers

None in the repository. `greenPotentialLInfinityFunctional` is used only by `GreenPotentialLInfinityFunctional.lean` and this file. No other file uses the four new names.

## Not claimed

No singular-source representative, no boundary regularity, no general-domain reciprocity, no compact-pole divergence (reserved to h2), no E51 or numbered closure, no physical exponent, no metric moment, no Pfeffer Def 1.6 membership or Prop 4.6, no literature input. `Φ x` is the literal Green integral on a representative, not an abstract kernel operator.

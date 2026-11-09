# Audit: BoundedDensityGreenStability

TASK: green-bounded-density-uniform-stability (worker q2, Claude Haiku 5.5)
FILE: `HarmonicBalls/Proofs/Potential/BoundedDensityGreenStability.lean` (151 lines, new)
STATUS: `lc` passes (`-DwarningAsError=true`), `lb` builds the module, all five declarations have printed axioms `[propext, Classical.choice, Quot.sound]`. Raw and comment-stripped scans for `sorry`, `axiom`, `admit`, `native_decide`, `maxHeartbeats`, `set_option`: 0 hits.

## Statements (carrier ℂ, measure `volume` on ℂ, `G_U(x, ·) = greenFunction U x : ℂ → ℝ`, zero-extended)

Common binders: `{U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)`.

| Declaration | Line | Conclusion (hypotheses in brackets) |
|---|---|---|
| `exists_greenFunction_row_integral_le` | 38 | `∃ C, 0 ≤ C ∧ ∀ x, Integrable (greenFunction U x) ∧ (∫ y, greenFunction U x y) ≤ C` |
| `integrable_greenFunction_mul_of_ae_bounded` | 56 | `(x) {f} (hf : AEStronglyMeasurable f volume) {M} (hfM : ∀ᵐ y, \|f y\| ≤ M)` ⊢ `Integrable (fun y => G x y * f y)` |
| `abs_integral_greenFunction_mul_sub_le_of_row_bound` | 67 | `{C} (hC : ∀ x, (∫ y, G x y) ≤ C) (x) {f g} …  {ε} (hε : 0 ≤ ε) (hfg : ∀ᵐ y, \|f y - g y\| ≤ ε)` ⊢ `\|∫ G x f - ∫ G x g\| ≤ C * ε` |
| `exists_greenPotential_boundedDensity_stability` | 98 | `∃ C, 0 ≤ C ∧ ∀ f g` (AE-strongly-measurable, each bounded a.e. by some `M ≥ 0`): integrability of `G x * f`, `G x * g` for every `x`, and for every `ε ≥ 0` with `\|f - g\| ≤ ε` a.e., `\|∫ G x f - ∫ G x g\| ≤ C * ε` for every `x` |
| `tendstoUniformly_greenPotential_of_ae_error` | 120 | `(hf : AEStronglyMeasurable f volume) (hfM : ∃ M, 0 ≤ M ∧ …) (F : ℕ → ℂ → ℝ)` with each `F n` AE-measurable and bounded a.e., `(ε : ℕ → ℝ) (hεF : ∀ n, ∀ᵐ y, \|F n y - f y\| ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))` ⊢ `TendstoUniformly (fun n x => ∫ G x * F n) (fun x => ∫ G x * f) atTop` |

Constants. The row constant is `K * R ^ 2 * (1 + |Real.log R|)`, where `K` comes from `exists_greenFunction_local_volume_bound` and `U ⊆ ball 0 R` from `Bornology.IsBounded.subset_ball_lt`. It depends on `U` only. The difference constant is the same `C`, so it is independent of the densities and of the pole. Nonnegativity of `ε n` in the last declaration is derived from the a.e. inequality (the measure on `ℂ` is nontrivial), not assumed. The nonnegativity hypothesis `0 ≤ ε` in the difference estimate is part of the requested statement.

## Providers (all committed before b7d689b)

- `exists_greenFunction_local_volume_bound`: `HarmonicBalls/Proofs/Potential/GreenLocalVolumeBound.lean` (committed 7007db1). Uniform in the pole `x` and the centre `c`.
- `integrable_greenFunction_pole`: `HarmonicBalls/Proofs/Potential/GreenPoleL1Continuity.lean:62` (committed 7b9c811).
- `greenFunction`: `HarmonicBalls/Defs/Green.lean:70`; `greenFunction_of_notMem_right`: `Defs/Green.lean:100` (zero off `O`); `greenFunction_nonneg`: `Defs/Green.lean:134` (needs only `IsBounded`).
- Mathlib: `Integrable.mul_bdd` (`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1073`), `Integrable.mul_const`, `abs_integral_le_integral_abs` (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:977`), `integral_mul_const` (`Bochner/Basic.lean:294`), `integral_sub`, `integral_mono_ae`, `setIntegral_eq_integral_of_forall_compl_eq_zero` (`Mathlib/MeasureTheory/Integral/Bochner/Set.lean:488`), `Metric.tendstoUniformly_iff` (`Mathlib/Topology/MetricSpace/Pseudo/Basic.lean:159`), `gt_mem_nhds`, `Filter.Eventually.exists`, `Integrable.congr`.

Search before duplicating. `exists_greenFunction_row_integral_le` and the other four declarations are new names; a grep of `HarmonicBalls` for each name finds no other declaration. `TransposedGreenMassBound.lean` (`disc_green_volume_row_bound`, `transposedGreen_mass_bound`) is stated for discs `B(0, R)` and was not used. Its statements were not compared to the general-`U` row bound beyond their binders. `Sec6/GreenUniformBound.lean` (`exists_uniform_bound_greenFunction`) was not inspected. The earlier file `BoundedDensityGreenContinuity` (1191fcd) was neither imported nor consumed.

## Import closure

Measured in Lean from the environment header (`env.header.moduleNames`) of a scratch file outside the repository (`/tmp/q2-bds/Closure.lean`, checked with `lc`):

- Direct import: `HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity`.
- Transitive closure, 11,796 modules: HarmonicBalls 352; Mathlib 8,536; MarkovProcess 152; LatticeProb 2 (`LatticeProb.Prob.Birkhoff`, `LatticeProb.Prob.MaximalErgodic`); Lean core and its packages (`Init`, `Std`, `Batteries`, `Aesop`, `Qq`, `Plausible`, `Lean`, others) 2,754 (the scratch file adds `import Lean`; Mathlib already imports it).

## Credit

The module docstring credits Leonardo Bonanno. His code reaches this file only through the pinned Lattice-Probability (lean-v4.35) port, visible here as `LatticeProb.Prob.Birkhoff` and `LatticeProb.Prob.MaximalErgodic` in the closure.

## Checks

- `lc` (`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true`) on the final source: `CHECK OK`, log `logs/lc/003314-3970520.log`.
- `lb HarmonicBalls.Proofs.Potential.BoundedDensityGreenStability` on the final source: exit 0, `.olean` written 00:34:01 (sandbox time).
- `#print axioms` for all five declarations (scratch `/tmp/q2-bds/AxCheck.lean`, outside the repository): `[propext, Classical.choice, Quot.sound]` each.
- Raw grep and comment-stripped grep of the file for `sorry|axiom|admit|native_decide|maxHeartbeats|set_option`: 0 hits.
- Names of the five declarations in `HarmonicBalls/**/*.lean` (other than this file): none. Consumers of this file in `HarmonicBalls` or `docs`: none.

## Remaining consumers and what is not claimed

- No consumer in the repository yet. Wiring to `Steps` or `Draft` consumers is operator routing.
- Not claimed: a normal representative of `G_U`, reciprocity for general domains, boundary regularity, the numbered E51 closure, physical exponents, metric moments, Pfeffer Def 1.6 or Prop 4.6, and any literature input. No `External` or `Proposed` module is imported.
- Interior continuity of the Green potential is not part of this file.

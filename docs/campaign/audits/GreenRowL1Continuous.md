# GreenRowL1Continuous audit

Task: green-row-continuous-L1-map (typed Mathlib L¹ carrier for the continuous Green row in the pole;
consumer of the scalar theorem committed in 7b9c811).

File: `HarmonicBalls/Proofs/Potential/GreenRowL1Continuous.lean` (new; namespace `HarmonicBalls`).

Carrier. `Lp ℝ 1 (volume : Measure ℂ)`, i.e. `ℂ →₁[volume] ℝ` (Mathlib `MeasureTheory.Lp`, Lebesgue measure on ℂ).
Standing binders of every declaration: `{U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)`.

Declarations (line numbers in the new file):
- l.37 `greenRowL1 hU hUb (x : ℂ) : Lp ℝ 1 volume := (integrable_greenFunction_pole hU hUb x).toL1 (greenFunction U x)`.
- l.42 `coeFn_greenRowL1 hU hUb x : ⇑(greenRowL1 hU hUb x) =ᵐ[volume] greenFunction U x` (`Integrable.coeFn_toL1`).
- l.48 `eq_greenRowL1_iff hU hUb x (φ : Lp ℝ 1 volume) : φ = greenRowL1 hU hUb x ↔ ⇑φ =ᵐ[volume] greenFunction U x`.
  Exact uniqueness of the representative under the a.e. characterization (`Lp.ext`, `EventuallyEq.trans`).
- l.59 `norm_greenRowL1_sub hU hUb x z : ‖greenRowL1 hU hUb x - greenRowL1 hU hUb z‖ = ∫ y, |greenFunction U x y - greenFunction U z y|`
  (`L1.norm_eq_integral_norm`, `Lp.coeFn_sub`, `integral_congr_ae`).
- l.69 `dist_greenRowL1 hU hUb x z`: the same integral for `dist` (`dist_eq_norm`).
- l.75 `continuousOn_greenRowL1 hU hUb : ContinuousOn (greenRowL1 hU hUb) U` (`ContinuousWithinAt`, `tendsto_iff_dist_tendsto_zero`).
- l.83 `uniformContinuousOn_greenRowL1 hU hUb {K : Set ℂ} (hKU : K ⊆ U) (hK : IsCompact K) : UniformContinuousOn (greenRowL1 hU hUb) K`
  (`IsCompact.uniformContinuousOn_of_continuous`, Mathlib `Topology/UniformSpace/HeineCantor.lean:49`).

Route. No new analysis, no kernel-continuity premise, no chosen representative. Integrability and continuity come only from:
- `integrable_greenFunction_pole` (`Proofs/Potential/GreenPoleL1Continuity.lean:62`): `y ↦ G_U(z, y)` is integrable for every pole `z : ℂ`;
- `tendsto_integral_abs_greenFunction_sub_nhdsWithin` (`GreenPoleL1Continuity.lean:229`): `∫ |G_U(z, ·) - G_U(x, ·)| → 0` along `𝓝[U] x` for `x ∈ U`
  (from `tendsto_integral_abs_greenFunction_sub`, l.194).
The diagonal convention is that of `greenFunction` (junk value `0` on `y = x`, a null set, `GreenPoleL1Continuity` audit). No statement about poles on `∂U`.

Not reused, not confused. `existsUnique_transposedGreen_L1_operator` (`Proofs/Potential/TransposedGreenL1Operator.lean:59`)
varies the source measure `ν` of a bounded operator on `L¹`; `greenRowL1` varies the pole `x` of the row. No declaration is shared.
Searched the repository for `greenRowL1`, `GreenRowL1` and `green-row-continuous` (task files included): no prior declaration.

Import closure. The file imports only `HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity`. Its import closure, computed on the
sandbox by a BFS over `import` lines: 351 HarmonicBalls modules; 48 distinct Mathlib modules; 12 external modules:
`LatticeProb.Prob.Birkhoff` (Lattice-Probability, pinned rev `3912597a` in `lake-manifest.json`) and 11 `MarkovProcess.*` modules.
The Bonanno credit in the module docstring refers to the first of these.

Consumers. In the repository, `GreenPoleL1Continuity`, `tendsto_integral_abs_greenFunction_sub` and `integrable_greenFunction_pole`
are used only in their own file. No declaration uses `greenRowL1` yet.

Checks (sandbox, this round):
- `lc` on the file (project options, `-DwarningAsError=true`): CHECK OK.
- `lb HarmonicBalls.Proofs.Potential.GreenRowL1Continuous`: BUILD OK; build log has 0 warnings, 0 errors.
- `#print axioms` for all seven declarations: `[propext, Classical.choice, Quot.sound]`.
- Raw scan for `sorry|axiom|admit|native_decide|maxHeartbeats|set_option|Heartbeat`: 0 hits (so the comment-aware scan is clean too).

Not in scope. Poles on `∂U`; L¹ continuity on all of `ℂ`; the normal-representative or boundary closure (E51).

# Audit: GreenBoundedAEDensityStability

Task `green-bounded-ae-density-compact-stability`. File: `HarmonicBalls/Proofs/Potential/GreenBoundedAEDensityStability.lean` (new, 171 lines).

## Status
- `lc` passes (log clean: no warnings, no errors); `lb HarmonicBalls.Proofs.Potential.GreenBoundedAEDensityStability` passes.
- `#print axioms` for all five declarations: `[propext, Classical.choice, Quot.sound]` only.
- Raw forbidden-token scan (sorry, axiom, admit, native_decide, unsafe, extern, maxHeartbeats, set_option, implemented_by, opaque, initialize, partial, decide): no matches.

## Literal carrier and formula
- Kernel: `greenFunction U x y : ℝ` (`HarmonicBalls/Defs/Green.lean:70`), with `U : Set ℂ`; value `0` off `U`
  (`greenFunction_of_notMem_left` :97, `greenFunction_of_notMem_right` :100) and nonnegative (`greenFunction_nonneg` :134).
- Densities: `f n g : ℂ → ℝ`, `AEStronglyMeasurable _ volume`, `|f n y| ≤ M` and `|g y| ≤ M` for volume-a.e. `y`,
  `f n y → g y` for volume-a.e. `y`. The common bound is one real `M` (no sign assumed; `|M|` is used).
- Potentials: the literal Bochner integrals `∫ y, greenFunction U x y * f n y` against `volume` on `ℂ`.
  No uniform-convergence hypothesis, no operator hypothesis, no literature input.

## Declarations (line numbers in the committed file)
- `tendsto_greenPotential_of_ae_convergence` (:37): pointwise convergence at every pole `x : ℂ` (dominated convergence,
  bound `|M| * greenFunction U x ·`).
- `abs_sub_lt_of_three_steps` (:59): real triangle estimate for the finite net.
- `tendstoUniformlyOn_greenPotential_of_ae_convergence` (:75): `TendstoUniformlyOn (fun n x => ∫ …f n…) (fun x => ∫ …g…) atTop K`
  for compact `K ⊆ U`.
- `exists_forall_abs_greenPotential_sub_lt_of_ae_convergence` (:128): for `0 < ε` there is `N` with `|P_n x - P x| < ε`
  for all `n ≥ N` and all `x ∈ K`.
- `greenPotential_boundedAE_convergence_compact` (:152): conjunction of integrability of every literal integrand (`f n` and
  `g`, for every pole), the uniform convergence on `K`, and the `ε/N` form.

## Providers used (exact)
- `integrable_greenFunction_mul_bdd` (`Proofs/Potential/BoundedDensityGreenContinuity.lean:33`).
- `abs_integral_greenFunction_mul_sub_le` (`BoundedDensityGreenContinuity.lean:44`): `|P_f x - P_f z| ≤ M * ∫ |G x - G z|`.
- `greenRowL1`, `dist_greenRowL1` (`Proofs/Potential/GreenRowL1Continuous.lean:37`, :69): `dist (greenRowL1 x) (greenRowL1 z) = ∫ |G x - G z|`.
- `uniformContinuousOn_greenRowL1` (`GreenRowL1Continuous.lean:83`): uniform continuity of the pole map into `L¹` on compact `K ⊆ U`.
- `integrable_greenFunction_pole` (`Proofs/Potential/GreenPoleL1Continuity.lean:62`).
- Mathlib: `tendsto_integral_of_dominated_convergence` (`MeasureTheory/Integral/DominatedConvergence.lean:57`),
  `finite_cover_balls_of_compact` (`Topology/MetricSpace/Pseudo/Basic.lean:263`), `Filter.eventually_all_finite`
  (`Order/Filter/Finite.lean:252`), `Metric.tendstoUniformlyOn_iff` (`Topology/MetricSpace/Pseudo/Basic.lean:144`),
  `Metric.uniformContinuousOn_iff` (`Topology/MetricSpace/Pseudo/Defs.lean:762`).

## Reuse search (done before proving)
- `BoundedDensityGreenStability.tendstoUniformly_greenPotential_of_ae_error` (`BoundedDensityGreenStability.lean:120`)
  needs a uniform error bound `|F n - f| ≤ ε n` a.e. with `ε n → 0` and gives uniform convergence on all of `ℂ`.
  It does not cover a.e. convergence on a compact set, so it is not duplicated; the new file does not import it.
- Mathlib equicontinuity providers (`Topology/UniformSpace/Ascoli.lean:334,362`, `EquicontinuousOn.tendsto_uniformOnFun_iff_pi`)
  are statements for the `uniformOnFun` topology. They are not used: the modulus here is an explicit `δ` from
  `uniformContinuousOn_greenRowL1`, and the finite-net `ε/3` argument is direct.

## Import closure and consumers
- Direct imports: `BoundedDensityGreenContinuity`, `GreenRowL1Continuous`; both import `GreenPoleL1Continuity`.
- Closure (`/tmp/q2-ax/closure.py`): 354 modules including self, none missing. `HarmonicBalls.Proposed.Birkhoff` and
  `HarmonicBalls.Proposed.LQG` occur in the closure through existing imports; no declaration here uses them
  (the axioms list shows no extra constants). `GreenPotentialFunctionalNorm`, `GreenRowUniformIntegrability` and
  `BoundedDensityGreenStability` are not in the closure.
- Remaining consumers: none (no file in `HarmonicBalls/` or `HarmonicBalls.lean` names the module).

## Credit
- The module docstring credits Leonardo Bonanno through the pinned Lattice-Probability (lean-v4.35) port, with the
  wording of `BoundedDensityGreenStability.lean`. No other channel is cited.

## Open items
- None for this task. Proof-level gaps: none found. No false printed statement encountered in the routed inputs.

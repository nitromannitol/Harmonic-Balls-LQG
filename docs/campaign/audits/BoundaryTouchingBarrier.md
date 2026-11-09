# Audit: BoundaryTouchingBarrier (task b1-finite-auxiliary-odometer-barrier)

Scope verdict: the finite-barrier construction of `steps4-t4.tex` lines 927-955 is formalized deterministically. Its only
non-derived input is the small-auxiliary-cluster premise `hsmall` (the separate small-time proposition, source lines
878-925), which is a hypothesis of the theorem and is not proved here. The proved obstacle regularity and the Green
singularity are reused from existing declarations.

## Target and source

- File: `HarmonicBalls/Proofs/Sec5/BoundaryTouchingBarrier.lean` (new, 259 lines).
- Source: `notes/wpn-steps4/steps4-t4.tex`, lines 927-955 (Comparison at a point separated from the old cluster).
  Premise `eq:small-auxiliary-cluster`: lines 878-925 (hypothesis here, not proved).
- Consumers, not changed here: `ClusterBoundaryTouchingRightContinuityStep` (`Steps/Sec5/ContinuityAssembly.lean:19`),
  used at `:39`, `:44`, and `Proofs/Sec5/StagedInputAssembly.lean:102-103` (Prop 5.2).

## Main theorem `HarmonicBalls.finite_auxiliary_barrier_boundary_touching`

Binders:
- `(μ : Measure ℂ) (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ} (hV : VolumeGrowth μ 4 βm βp)`: properties of the actual
  measure on the event (Radon, volume growth on `B_4`).
- `{p : ℂ} (hp : p ∈ closedBall 0 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1/8)`.
- `(hsmall : ∀ q ∈ sphere p r ∩ closedBall 0 1, ∃ σ : ℝ, 0 < σ ∧ closure (cluster μ 4 q σ) ⊆ ball q (r/4))`.

Conclusion, with `E = ball p r ∩ ball 0 1` and `S = sphere p r ∩ closedBall 0 1`: there are `T : Finset ℂ`,
`σ : ℂ → ℝ`, `H : ℂ → ℝ` with
- `1 ≤ T.card`; `∀ q ∈ T, q ∈ S`; `∀ q ∈ T, 0 < σ q`;
- `H = fun x => ∑ q ∈ T, odometer μ 4 q (σ q) x` (the literal finite sum of actual odometers);
- `∀ x ∈ E, 0 ≤ H x`; `ContinuousOn H E`;
- `∀ x ∈ E ∩ ball p (r/2), H x = 0`;
- `∃ c > 0, ∀ x ∈ S, (∀ q ∈ T, x ≠ q) → c ≤ H x`;
- `∀ q ∈ T, Tendsto H (𝓝[≠] q) atTop`;
- `LaplacianLE H (T.card • μ) E`.

Inputs used: `hsmall`, `hμ`, `hV`. No literature Prop, no `Proposed`/`External` Prop, no Draft `…Stmt` is a binder.

## Paper-to-Lean map

| Paper step | Lean declaration (file) |
|---|---|
| actual odometer `b_q`, pole value unchanged | `odometer` (`Defs/Obstacle.lean:76`); no extended function |
| least supersolution finite, continuous on closed ball (Lemma 3.1) | `leastSupersolution_mem_of_general` (`Steps/Sec3/LeastSupersolutionMem.lean:33`), instantiated with `obstacleLeastSuperharmonicMajorantGeneral_holds` (`Proofs/SecA/ObstacleNonCoincidenceHarmonic.lean:545`) and `obstacleCompatibilityShiftStep_holds` (`Proofs/Sec3/Basic.lean:116`) |
| Green singularity, divergence at the pole | `tendsto_greenFunction_ball_pole` (`Proofs/Sec8/GreenKernelContinuity.lean:18`) |
| divergence of the odometer at its pole | `tendsto_odometer_pole_atTop` (this file) |
| off-pole continuity | `continuousOn_odometer_off_pole` (this file; uses `continuousOn_greenFunction_ball`, `Proofs/Potential/GreenBall.lean:331`) |
| nonnegativity | `odometer_nonneg` (`Defs/Obstacle.lean:161`) |
| vanishing in the inner lens | `odometer_eq_zero_of_not_mem_cluster_ball` (this file; `mem_cluster_iff`, `Defs/Obstacle.lean:168`) |
| distributional bound `Δb ≤ μ` away from the pole | `Section6.odometer_hasLaplacian_dominated_away_from_pole` (`Proofs/Sec6/AnnulusOdometerPotential.lean:66`), wrapped as `laplacianLE_odometer_of_open` |
| sum of bounds | `laplacianLE_add_measure`, `laplacianLE_finset_sum` (this file; uses `integrable_mul_laplacian_of_test`, `Steps/Sec3/Basic.lean:113`) |
| finite positivity cover of compact `S` | `IsCompact.elim_nhds_subcover` on radii `ρ_q` with odometer `≥ 1` on the punctured ball |
| `N ≥ 1` | `sphere_inter_closedBall_nonempty` (this file) |

Lower bound: the paper uses `+∞` at the poles and `c > 0` on `S`. Here the real-valued odometer is used with its own pole
value. For `x ∈ S` not a pole, `x` lies in some cover ball `B(q, ρ_q)`, `x ≠ q`, so `H x ≥ odometer q x ≥ 1` (other terms
are nonnegative). Hence `c = 1`.

Lower limits: at each pole `q ∈ T`, the odometer of `q` tends to `+∞` (divergence), the other summands are eventually
nonnegative in `𝓝[≠] q` (finitely many other poles avoided), so `tendsto_atTop_mono'` gives `H → +∞`.

## Checks

- `lc` on the file: OK (warnings as errors).
- `lb HarmonicBalls.Proofs.Sec5.BoundaryTouchingBarrier`: exit 0.
- Printed axioms (scratch `/tmp/q2-ax/AxB1.lean`, not committed): all seven checked declarations depend only on
  `[propext, Classical.choice, Quot.sound]`, including the main theorem.
- Raw token scan (`sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, `extern`, `implemented_by`, `opaque`,
  `maxHeartbeats`, `maxRecDepth`, `set_option`, `Lean.ofReduceBool`): 0 hits.
- Import closure (transitive, via `import` lines): 124 HarmonicBalls modules including self. `Proposed/Birkhoff.lean` and
  `Proposed/LQG.lean` are in the closure only through existing imports; the file references no `Proposed` declaration and
  takes no `Proposed` Prop as a hypothesis. `External`: 0. `Audit`: 0. `Draft`: 10, through existing imports only; no Draft
  statement is a binder.

## Credit

Module docstring credits Leonardo Bonanno through the pinned Lattice-Probability (lean-v4.35) port, wording as in
`Proofs/Potential/BoundedDensityGreenStability.lean`. The Green-ball lemmas used (`continuousOn_greenFunction_ball`,
`tendsto_greenFunction_ball_pole`) are reached through `Proofs/Potential/GreenBall` and `Proofs/Sec8` imports.

## Decisions for operator redirect

1. `c = 1` rather than a compactness minimum: the divergence radii give `H ≥ 1` on `S` minus poles directly.
2. The odometer's own pole value is kept. The paper's `+∞` convention enters only through the divergence statement.
3. Poles form a `Finset T`; `N = T.card`; masses are `σ : ℂ → ℝ`. An equivalent `Fin N`-indexed form is not stated.
4. `hμ`, `hV` are binders: deterministic properties of the actual measure on the event, not derived here.
5. `hsmall` is the premise (paper `eq:small-auxiliary-cluster` with `a = r/4`), a hypothesis, not proved here.

## Remaining (outside this packet)

- Small-cluster event (source 878-925): separate Lean work.
- Maximum comparison and local persistence (source 957-994); final compactness (source 996-1006): separate.
- `ClusterBoundaryTouchingRightContinuityStep` and the Prop 5.2 consumers are unchanged.

## Ownership

Committed: `HarmonicBalls/Proofs/Sec5/BoundaryTouchingBarrier.lean` (new), `docs/campaign/audits/BoundaryTouchingBarrier.md`
(new). No Defs, Draft, FROZEN, External, Proposed, paper, lakefile, `.lake`, or `HarmonicBalls.lean` change.

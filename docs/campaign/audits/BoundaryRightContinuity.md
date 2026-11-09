# Audit: BoundaryRightContinuity (Proposition 5.2, boundary-touching step)

Target: `HarmonicBalls.ClusterBoundaryTouchingRightContinuityStep` (Steps/Sec5/ContinuityAssembly.lean:19).
Consumer: `clusterContinuity_of_boundaryTouching` (ContinuityAssembly.lean:44).
Written source: fleet `notes/wpn-steps4/steps4-final.tex` (sha256 f9da848c...), Section 4, lines 1161-1228 (stage 1,
eq:local-persistence-zero) and 1230-1253 (stage 2). The written argument was checked against the Lean definitions
(cluster, odometer, supersolutions, `LaplacianLE`, `HasLaplacian`); no gap was found.

File: `HarmonicBalls/Proofs/Sec5/BoundaryRightContinuity.lean`.
Commits: 27fcc2e (stage 1), a6ae6ba (stage 2 and consumers). Build: `lb` OK, 0 errors.
Printed axioms (all four theorems below): `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`,
`native_decide`, new axiom, or heartbeat override.

## Declarations

- `local_persistence` (stage 1). For `z` in the open unit disc, `t > 0`, `p` in the closed disc with
  `p ∉ closure (cluster μ 1 z t)`: there are `r, δ > 0` such that the cluster at `t + s`, `0 ≤ s ≤ δ`, avoids
  `ball p (r/2)`. Inputs: `hμ`, `hVR`, `hsmall`.
- `odometer_le_mul_on_ball` (comparison at one time). With `u = odometer μ 1 z τ`, `F = u - κH` on
  `U = ball p r ∩ ball 0 1`, the barrier `H` of `finite_auxiliary_barrier_boundary_touching`: `u ≤ κH` on `U`.
  Route: positivity set `Λ = {x ∈ U | F x > 0}`; active identity `HasLaplacian u (μ|Λ) 0 Λ`
  (`Section6.odometer_hasLaplacian_on_cluster`); sum rule `laplacianGE_sub_of_hasLaplacian` (own lemma,
  uses `κ N ≤ 1`); gluing `Section6.laplacianGE_indicator_of_zero_frontier` on `Λ.indicator (max F 0)`;
  bridge `isSubharmonicOn_of_laplacianGE_zero`; maximum principle
  `isSubharmonicOn_ball_sdiff_le_of_eventually_lt` with removed set `K = {x | 1 ≤ ‖x‖} ∪ T` (T the poles)
  and level `η > 0`, then `η → 0`. The Green-function boundary behaviour comes from `greenFunctionBall`
  (`GreenFunctionBallStmt`, Steps/Sec2/GreenFunctionBall.lean:156, a proved term).
- `closure_cluster_small_of_local` (stage 2). For every `ε > 0` there is `δ > 0` with
  `closure (cluster μ 1 z t') ⊆ cluster μ 1 z t + ball 0 ε` for `t' ∈ Icc t (t + δ)`. Compactness of
  `L = closedBall 0 1 \ (cluster + ball 0 ε)`, finite subcover by stage-1 balls, uniform `δ` by
  `exists_pos_le_finset`.
- `clusterBoundaryTouching_of_fields` (CONDITIONAL). Proves `ClusterBoundaryTouchingRightContinuityStep`
  from `h71` and the explicit field inputs listed below. This is a conditional assembly, not a numbered closure.
- `clusterContinuity_of_staged` (CONDITIONAL). `ClusterContinuityStmt` from `h71 h33 h72` and the same
  field inputs, through `clusterContinuity_of_boundaryTouching`.

## Hypotheses actually used (none is new)

| binder | Lean type | source |
|---|---|---|
| `h71` | `ClusterUpperBoundPolyHighProbStmt` | Draft/Section7.lean:51 (numbered predecessor) |
| `h33`, `h72` | `ClusterMonotoneStmt`, `ClusterTimeContinuityStmt` | consumer only |
| `hDG` | `∀ Ω P γ hC hcirc, WholePlaneLQGBallMassBounds P γ hC hcirc` | Proposed/LQG.lean:152 (Ding-Gwynne 2020, Lemma 3.8, per Proofs/Sec2/Assembly.lean docstring) |
| `hAff` | `∀ Ω P hC hcirc, WholePlaneGFFAffineInvariance P hC hcirc` | Proposed/LQG.lean:51 |
| `hCC` | `∀ Ω P γ α₀ hC hcirc, LQGMeasureCoordChange P γ α₀ hC hcirc` | Proposed/LQG.lean:114 |
| `hW` | `∀ Ω P γ hC hcirc, LQGMeasureWeylScaling P γ 0 hC hcirc` | Proposed/LQG.lean:93 |
| `hE` | `∀ Ω P γ hC hcirc, LQGMeasureExistence P γ 0 hC hcirc` | Proposed/LQG.lean:66 |
| `hN` | `∀ Ω P γ α₀ hC hcirc, LQGMeasureNonatomic P γ α₀ hC hcirc` | Proposed/LQG.lean:75 |

Proposed inputs are pending operator source-check. Nothing is staged that is not already in Proposed/LQG.lean.

## Why `hDG`, `hW`, `hE`, `hN` are needed (point for the operator)

The finite barrier and every odometer lemma take `VolumeGrowth μ R βm βp` (almost surely, for all radii).
That fact is only available through `LQGVolumeGrowthAllScalesStmt` (I2). The Lean route is
`lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN` (Proofs/Sec2/Assembly.lean:120), which
uses the proved mixture step `wholePlaneGFFMixtureStep_holds`. The other route,
`wholePlaneScaledBallMassStep_of_rescaled`, needs `RescaledBallMassUniformStep`, which is not proved in the
repository. So the target is not closed from `h71`, `hAff`, `hCC` alone: `hDG`, `hW`, `hE`, `hN` are also
required.

## Points that are not used

- The hypothesis `¬ closure (cluster μ 1 z t) ⊆ ball 0 1` of the target. The comparison is uniform in `t`.
- The paper's claim that the least supersolution vanishes on `∂B_1` (steps4 line ~1100). Lean uses the
  boundary limit of `greenFunctionBall` and the cluster-zero outside the cluster in `B_1`.

## Credit

Leonardo Bonanno: the small-cluster event `SmallAuxiliaryClusterEvent.lean` consumes his Lattice-Probability
formalization on the pinned lean-v4.35 line (`lakefile.lean`, commit 3912597a70dcc6c9b73042abd884a26989341c8d),
through the import closure of `LatticeProb.Prob.Birkhoff`. The module docstring cites him.

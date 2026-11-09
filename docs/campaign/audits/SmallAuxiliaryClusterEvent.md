# Audit: `ae_radiusFour_cluster_small_all_centres`

Task `b1-radius-four-small-auxiliary-cluster-event` (worker q2). Status: DONE, committed on main, not pushed.

## Declaration

- `HarmonicBalls.ae_radiusFour_cluster_small_all_centres` in
  `HarmonicBalls/Proofs/Sec5/SmallAuxiliaryClusterEvent.lean` (module `HarmonicBalls.Proofs.Sec5.SmallAuxiliaryClusterEvent`).
- Conclusion, with the event first and then every pole and every radius:
  `∀ᵐ ω ∂P, ∀ q ∈ closedBall (0 : ℂ) 1, ∀ a : ℝ, 0 < a → ∃ σ : ℝ, 0 < σ ∧ closure (cluster (μ ω) 4 q σ) ⊆ ball q a`.
- Binders, all existing (no new input admitted):
  - `Ω : Type u`, `[MeasurableSpace Ω]`, `P : Measure Ω`, `γ α₀ : ℝ`, `hC : Ω → (ℂ → ℝ) → ℝ`, `hcirc : Ω → ℝ → ℂ → ℝ`, `μ : Ω → Measure ℂ`.
  - `h71 : ClusterUpperBoundPolyHighProbStmt.{u}`: `HarmonicBalls/Draft/Section7.lean:51` (numbered predecessor, Proposition 7.1, pp. 37-38 of the source).
  - `hAff : WholePlaneGFFAffineInvariance P hC hcirc`: `HarmonicBalls/Proposed/LQG.lean:51` (Proposed; pending operator source-check).
  - `hCC : LQGMeasureCoordChange P γ α₀ hC hcirc`: `HarmonicBalls/Proposed/LQG.lean:114` (Proposed; pending operator source-check).
  - `hγ : 0 < γ`, `hγ2 : γ < 2`, `hα : α₀ < lqgQ γ`, `hGFF : IsWholePlaneGFF P hC hcirc`, `hμ : IsLQGMeasureOfField P γ α₀ hcirc μ`.

## Source and route

- Written argument: `notes/wpn-steps4/steps4-final.tex` lines 1112-1159 (SHA f9da848c8ad8179d8fd94795b7bfbdf198d7e8aefd38c72c89788a56acdba932, authoritative). The task's copy, `steps4-t4.tex` lines 878-925, has the same text.
  Checked against it: `h'(x) = h(4x) - h_4(0)`; `m'(E) = A^{-1} μ(4E)` with `A = exp(γ h_4(0)) 4^{γQ}`; `4^{-1} cluster(μ,4,q,A s) = cluster(m',1,q/4,s)`; poles `q/4` in `B_{1/2}`.
- Lean route: the radius-one proof `ae_disc_cluster_small_open_neighborhoods_all_centres` (`HarmonicBalls/Proofs/Sec5/AllCentrePunctureInadmissibility.lean:34`) with the factor 2 replaced by 4 and closed-disc poles.
  1. `hC' := affinePairing hC hcirc 4 0`; `hcirc'` is the circle average of `h(4·) - h_4(0)`. `hGFF'` comes from `hAff` at `a = 4`, `b = 0`, via `affineCircle`.
  2. `hμ' : IsLQGMeasureOfField P γ α₀ hcirc' (normalizedPullbackMeasure γ α₀ 4 (hcirc ω) (μ ω))` from `isLQGMeasureOfField_normalizedPullback` (`HarmonicBalls/Proofs/Sec5/ScalingMeasure.lean:25`, generic in `k > 0`).
  3. For each `n : ℕ`, `h71` at radius `r_n = (2⁻¹)^n / 2 ∈ (0,1)` and `PolyHighProb.ae_eventually_dyadic` (`HarmonicBalls/Proofs/Sec2/PolyHighProb.lean:75`) give, almost surely, some `T > 0` with `closure (cluster (μ'_ω) 1 z t) ⊆ ball z (r_n / 2)` for all `t ∈ (0,T]` and `z ∈ ball 0 (1/2)`. A countable intersection (`ae_all_iff`) fixes one event for all `n`.
  4. For `q ∈ closedBall 0 1` and `a > 0`: choose `n` with `(2⁻¹)^n < a`; apply step 3 at `z = 4⁻¹ • q` (norm at most `1/4 < 1/2`) and time `T/2`; set `σ = c * (T/2)` with `c = exp(γ (lqgQ γ * log 4 + fieldCircleAverage α₀ (hcirc ω) 4 0))`.
     `cluster_normalizedPullback_smul` (`HarmonicBalls/Proofs/Sec5/ClusterGeometricScaling.lean:12`, `k = 4`, `R = 1`) gives `4 • cluster(μ'_ω) 1 (q/4) (σ/c) = cluster (μ ω) 4 q σ`.
     `closure_smul₀'` and `smul_set_mono` move the bound to `ball q (4 * (r_n/2)) = ball q ((2⁻¹)^n) ⊆ ball q a`.
- No radius-four small-cluster event, boundary-mass-zero statement, Proposition 5.2, B1, or compact containment of an old cluster is assumed. The radius-four cluster is obtained directly by scaling, so the radius-one monotonicity step is not needed.

## Consumer match

- `HarmonicBalls/Proofs/Sec5/BoundaryTouchingBarrier.lean:140-141`: `hsmall : ∀ q ∈ sphere p r ∩ closedBall (0 : ℂ) 1, ∃ σ : ℝ, 0 < σ ∧ closure (cluster μ 4 q σ) ⊆ ball q (r / 4)`.
  With `a = r / 4 > 0`, the theorem gives this for every pole of `closedBall 0 1` at every `ω` of the event. No pole is reindexed, so the odometer's actual pole values are used.
  The wiring (fixing `ω` and taking `μ = μ ω`) is not done here: `BoundaryTouchingBarrier.lean` is not owned by this task.
- Not proved here: local maximum comparison and persistence (`BoundaryTouchingBarrier.lean` 957-994), final compactness (996-1006), `ClusterBoundaryTouchingRightContinuityStep`, Proposition 5.2.

## Checks

- `lc HarmonicBalls/Proofs/Sec5/SmallAuxiliaryClusterEvent.lean`: CHECK OK (log `logs/lc/052323-1155415.log`).
- `lb HarmonicBalls.Proofs.Sec5.SmallAuxiliaryClusterEvent`: BUILD OK (log `logs/lb/052336-1182085.log`).
- Printed axioms of `HarmonicBalls.ae_radiusFour_cluster_small_all_centres`: `[propext, Classical.choice, Quot.sound]`.
- Token scans, raw and comment-aware: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `extern`, `implemented_by`, `opaque`, `set_option`, `maxHeartbeats`, `maxRecDepth`, `initialize`, `#exit`: no match. The only match is the `#print axioms` line.
- Credit: Leonardo Bonanno, through the pinned Lattice-Probability lean-v4.35 line (`lakefile.lean`, commit 3912597a70dcc6c9b73042abd884a26989341c8d). `LatticeProb.Prob.Birkhoff` lies in the import closure of the module (208 HarmonicBalls modules walked). The module docstring carries the credit.

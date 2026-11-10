import HarmonicBalls.FirstPass.S11r.RootedRootFinite

/-!
# First pass, rooted decoder: side conditions of the rooted gluing (fp-S11r, owner n2; R2 steps D-A..D-C)

Two side conditions of `eq_const_mul_internal_of_local_agreement` (RootedRepair.lean) that do not depend on the open
decoder-length question (D-A):
* `rootedWeight_continuousOn`: the rooted weight `-α log|·| - γ log|· - z| + γ log max(1, |·|)` (equation (20) of
  `LocalMetricReplacementStmt`) is continuous on `D ∖ {z}` when `0 ∉ D`, so `hfc` of `RootedRootFinite.lean` holds in the
  application (the statement of `LocalMetricReplacementStmt` assumes `0 ∉ closedBall c₂ r₂`).
* `decoder_tendsto_root`: a length metric `d` satisfies `d(x, z) → 0` as `x → z` (its topology is Euclidean), which is the
  input `hd_cont` of the gluing.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- The rooted weight `f_z = -α log|·| - γ log|· - z| + γ log max(1, |·|)` is continuous on `D ∖ {z}` when `0 ∉ D`. -/
theorem rootedWeight_continuousOn {D : Set ℂ} {z : ℂ} (hD0 : (0 : ℂ) ∉ D) (α γ : ℝ) :
    ContinuousOn (fun w : ℂ => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))
      (D \ {z}) := by
  have h0 : ∀ w ∈ D \ {z}, ‖w‖ ≠ 0 := fun w hw h => hD0 (norm_eq_zero.1 h ▸ hw.1)
  have h1 : ∀ w ∈ D \ {z}, ‖w - z‖ ≠ 0 := fun w hw h =>
    hw.2 (mem_singleton_iff.2 (sub_eq_zero.1 (norm_eq_zero.1 h)))
  have h2 : ∀ w ∈ D \ {z}, max 1 ‖w‖ ≠ 0 := fun w _ h => by
    have : (0 : ℝ) < max 1 ‖w‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    exact this.ne' h
  have hc1 : ContinuousOn (fun w : ℂ => ‖w‖) (D \ {z}) := continuous_norm.continuousOn
  have hc2 : ContinuousOn (fun w : ℂ => ‖w - z‖) (D \ {z}) :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  have hc3 : ContinuousOn (fun w : ℂ => max 1 ‖w‖) (D \ {z}) :=
    (continuous_const.max continuous_norm).continuousOn
  exact (((continuousOn_const.mul (hc1.log h0)).sub (continuousOn_const.mul (hc2.log h1))).add
    (continuousOn_const.mul (hc3.log h2)))

/-- A length metric tends to `0` at its base point: `d(x, z) → 0` as `x → z` (Euclidean topology, `isOpen_dist_lt_set`). -/
theorem decoder_tendsto_root {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (z : ℂ) (D : Set ℂ) :
    Tendsto (fun x => d x z) (𝓝[D] z) (𝓝 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hz : z ∈ {v | d z v < ε} := by
    rw [mem_ofPred_eq, hd.self_eq_zero z]
    exact hε
  filter_upwards [(isOpen_dist_lt_set hd z ε).mem_nhds hz] with x hx
  rw [Real.dist_eq, sub_zero, abs_lt]
  have hsym : d x z = d z x := hd.symm x z
  have hnn : 0 ≤ d z x := by
    have h := hd.triangle z x z
    rw [hd.self_eq_zero z] at h
    linarith [hd.symm x z]
  constructor
  · linarith
  · rw [hsym]
    exact hx

end HarmonicBalls

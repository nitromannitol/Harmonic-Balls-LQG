import HarmonicBalls.FirstPass.Phase2.RootedInternalDiagonal
import HarmonicBalls.FirstPass.Phase2.InternalMetricFineChains
import HarmonicBalls.FirstPass.S11r.RootedRootFinite
import LatticeProb.Topology.LocalAgreementChainsAt

/-!
# The rooted internal metric of a disk: metric properties for the gluing

Let `d` be a Euclidean length metric, `D = ball c r` with `closedBall c r ⊆ ball 0 1` and `0 ∉ closedBall c r`, `z ∈ D`,
and `k = -α log|·| - γ log|· - z| + γ log max(1, |·|)` the rooted weight. Write `E = weylPhysicalE d ξ k` for the Weyl
scaling of `d` by `k` and `D(·,·; D) = internalMetric E D` for its internal metric on `D`. If the Weyl scaling tends to
`0` at the root, then for every constant `b < ∞` the function `b · D(·,·; D)` is symmetric (`rootedInternal_symm`),
satisfies the triangle inequality on `D` (`rootedInternal_triangle`), tends to `0` along the diagonal of `D`
(`rootedInternal_diag`) and has fine chains in `D` between any two points of `D` (`rootedInternal_fineChainsAt`, in the
sense of `LatticeProb.Topology.HasFineChainsAt`). These are the hypotheses on the second function of the dense gluing
lemma for local agreement.

Terminology: internal metric (Armstrong-Kuusi-Mourrat); Weyl scaling and rooted (quantum-typical) point
(Duplantier-Sheffield; Dubédat-Falconet-Gwynne-Pfeffer-Sun).
-/

namespace HarmonicBalls

open Set Filter Topology Metric
open scoped ENNReal

namespace RootedLocal

/-- The rooted weight `-α log|·| - γ log|· - z| + γ log max(1, |·|)` is continuous on a disk avoiding `0`, off the
root `z`. -/
theorem continuousOn_rootedWeight (α γ : ℝ) {c z : ℂ} {r : ℝ} (h0 : (0 : ℂ) ∉ closedBall c r) :
    ContinuousOn (fun w : ℂ => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))
      (ball c r \ {z}) := by
  have h0' : ∀ w ∈ ball c r \ {z}, ‖w‖ ≠ 0 := fun w hw =>
    norm_ne_zero_iff.2 fun hw0 => h0 (hw0 ▸ ball_subset_closedBall hw.1)
  have h1' : ∀ w ∈ ball c r \ {z}, ‖w - z‖ ≠ 0 := fun w hw =>
    norm_ne_zero_iff.2 (sub_ne_zero.2 hw.2)
  have h2' : ∀ w ∈ ball c r \ {z}, max 1 ‖w‖ ≠ 0 := fun w _ =>
    (lt_max_of_lt_left one_pos).ne'
  exact ((continuousOn_const.mul (continuous_norm.continuousOn.log h0')).sub
    (continuousOn_const.mul ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn.log h1'))).add
    (continuousOn_const.mul ((continuous_const.max continuous_norm).continuousOn.log h2'))

variable {d : ℂ → ℂ → ℝ}

/-- **Symmetry.** `b · D(·,·; U)` is symmetric for the Weyl scaling of a Euclidean length metric by any weight. -/
theorem rootedInternal_symm (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (k : ℂ → ℝ) (U : Set ℂ) (b : ℝ≥0∞) :
    ∀ x ∈ U, ∀ y ∈ U, b * internalMetric (weylPhysicalE d ξ k) U x y =
      b * internalMetric (weylPhysicalE d ξ k) U y x := fun x _ y _ => by
  rw [internalMetric_symm_of_symm (weylPhysicalE_symm hd ξ k) U x y]

/-- **Triangle inequality.** If the Weyl scaling by the rooted weight tends to `0` at the root `z ∈ D`, then
`b · D(·,·; D)` satisfies the triangle inequality on `D = ball c r`. -/
theorem rootedInternal_triangle (hd : IsEuclideanLengthMetric d) (ξ α γ : ℝ) {c z : ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∉ closedBall c r) (hz : z ∈ ball c r)
    (hW : Tendsto (fun x => weylScaling d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) x z) (𝓝 z) (𝓝 0))
    (b : ℝ≥0∞) :
    ∀ x ∈ ball c r, ∀ y ∈ ball c r, ∀ w ∈ ball c r,
      b * internalMetric (weylPhysicalE d ξ
          (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) (ball c r) x w ≤
        b * internalMetric (weylPhysicalE d ξ
          (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) (ball c r) x y +
        b * internalMetric (weylPhysicalE d ξ
          (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) (ball c r) y w := by
  obtain ⟨hWD, -⟩ := finite_on_disk_root hd ξ isOpen_ball ((convex_ball c r).isConnected ⟨z, hz⟩) hz
    (continuousOn_rootedWeight α γ h0) hW
  intro x _ y _ w _
  rw [← mul_add]
  gcongr
  exact internalMetric_triangle_on _ (weylPhysicalE_symm hd ξ _) (fun x _ => weylPhysicalE_self hd ξ _ x)
    (weylPhysicalE_tri_of_finite hd ξ hWD)

/-- **Diagonal limit.** If the Weyl scaling by the rooted weight tends to `0` at the root `z ∈ D` and `b < ∞`, then
`b · D(u, p; D) → 0` as `u → p` within `D`, for every `p ∈ D = ball c r`. -/
theorem rootedInternal_diag (hd : IsEuclideanLengthMetric d) (ξ α γ : ℝ) {c z : ℂ} {r : ℝ}
    (hcD : closedBall c r ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r) (hz : z ∈ ball c r)
    (hW : Tendsto (fun x => weylScaling d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) x z) (𝓝 z) (𝓝 0))
    {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    ∀ p ∈ ball c r, Tendsto (fun u => b * internalMetric (weylPhysicalE d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) (ball c r) u p)
      (𝓝[ball c r] p) (𝓝 0) := fun p hp => by
  simpa only [mul_zero] using
    ENNReal.Tendsto.const_mul (tendsto_internalMetric_rootedWeight_diag hd ξ α γ hcD h0 hz hW p hp) (Or.inr hb)

/-- **Fine chains.** For any `e` and `b < ∞`, the function `b · D(·,·; D)` has fine chains in the disk `D` between any
two of its points. -/
theorem rootedInternal_fineChainsAt (e : ℂ → ℂ → ℝ) (c : ℂ) (r : ℝ) {b : ℝ≥0∞} (hb : b ≠ ⊤) :
    ∀ x ∈ ball c r, ∀ y ∈ ball c r,
      LatticeProb.Topology.HasFineChainsAt (ball c r) (fun u v => b * internalMetric e (ball c r) u v) x y :=
  fun x hx y hy => internalMetric_fineChains e ((convex_ball c r).isPathConnected ⟨x, hx⟩) hb x hx y hy

end RootedLocal

end HarmonicBalls

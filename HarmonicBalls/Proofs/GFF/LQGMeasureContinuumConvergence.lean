import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.LQGBallMassGrid2

/-!
# Continuum convergence of whole-plane GMC test integrals

The circle-average approximations of a whole-plane Gaussian free field converge at all positive
radii to the dyadic LQG measure when tested against a fixed continuous compactly supported function.
-/

open MeasureTheory Filter Topology Set
open LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- For a fixed compactly supported continuous test, the whole-plane circle-average GMC
approximations converge as the radius tends to zero through positive values. -/
theorem ae_tendsto_integral_lqgApprox_continuum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasure P γ hcirc μ) {g : ℂ → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => ∫ z, g z ∂(lqgApprox γ (hcirc ω) s))
      (𝓝[>] 0) (𝓝 (∫ z, g z ∂(μ ω))) := by
  filter_upwards [hh.ae_exists_tendsto_zero_integral_lqgApprox_sub hγ0 hγ2 hgc hgs, hμ] with ω hu hm
  obtain ⟨u, hu, hb⟩ := hu
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hu' := (Metric.tendsto_atTop.mp hu) (ε / 2) (half_pos hε)
  have hm' := (Metric.tendsto_atTop.mp (hm.tendsto_integral g hgc hgs)) (ε / 2) (half_pos hε)
  obtain ⟨N₁, hN₁⟩ := hu'
  obtain ⟨N₂, hN₂⟩ := hm'
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hb
  let N := max N₁ (max N₂ N₃)
  refine ⟨min 1 (dyadicScale N), lt_min (by norm_num) (dyadicScale_pos_bracket N), ?_⟩
  intro s hs hdist
  have hs0 : 0 < s := hs
  have hsmin : s < min 1 (dyadicScale N) := by simpa [Real.dist_eq, abs_of_pos hs0] using hdist
  obtain ⟨k, hk₁, hk₂⟩ := exists_dyadicScale_bracket hs0 (lt_of_lt_of_le hsmin (min_le_left _ _))
  have hNk : N ≤ k := by
    by_contra h
    have hle : k + 1 ≤ N := by omega
    have := dyadicScale_le_of_le hle
    linarith [lt_of_lt_of_le hsmin (min_le_right (1 : ℝ) (dyadicScale N))]
  have hband := hN₃ k (le_trans (le_trans (le_max_right N₂ N₃) (le_max_right N₁ _)) hNk)
    s (by simpa [dyadicScale_succ_eq_half] using hk₁) hk₂.le
  have huval := hN₁ k (le_trans (le_max_left N₁ _) hNk)
  have hmval := hN₂ k (le_trans (le_trans (le_max_left N₂ N₃) (le_max_right N₁ _)) hNk)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_trans (abs_nonneg _) hband)] at huval
  rw [Real.dist_eq] at hmval ⊢
  calc
    |(∫ z, g z ∂(lqgApprox γ (hcirc ω) s)) - ∫ z, g z ∂(μ ω)| ≤
        |(∫ z, g z ∂(lqgApprox γ (hcirc ω) s)) - ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))| +
        |(∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) - ∫ z, g z ∂(μ ω)| := abs_sub_le _ _ _
    _ < ε := by linarith

end HarmonicBalls

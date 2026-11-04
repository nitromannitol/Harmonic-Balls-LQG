import HarmonicBalls.Proofs.Sec10.UniformPoleNeighborhood

/-!
# Crossing estimates on compact subdiscs

A pole close to a crossing center in a compact subdisc lies in a slightly
larger compact subdisc. This removes both localization margins for such
centers when the mass is bounded away from zero.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A pole outside the domain gives the empty cluster at nonnegative mass. -/
theorem cluster_eq_empty_of_pole_not_mem {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hz : z ∉ ball (0 : ℂ) r) (ht : 0 ≤ t) : cluster μ r z t = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [mem_cluster_iff] at hx
  have hxz : x ≠ z := fun h => hz (h ▸ hx.1)
  have hG : greenFunction (ball 0 r) z x = 0 := greenFunction_of_notMem_left hz x
  have hlo := le_leastSupersolution (μ := μ) ht (ball_subset_closedBall hx.1) hxz
  have hhi := leastSupersolution_nonpos (μ := μ) ht (ball_subset_closedBall hx.1) hxz
  rw [hG] at hlo
  have hv : leastSupersolution μ r z t x = 0 := by linarith
  rcases hx.2 with h | h
  · exact hxz h
  · unfold odometer at h
    rw [hG, hv] at h
    simp at h

/-- At nonzero crossing centers in a fixed compact subdisc, the exact-radius
bound holds uniformly for all poles and all masses above a fixed positive
threshold. -/
theorem ae_compact_centers_crossings_above_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b t₀ : ℝ, b < 1 → 0 < t₀ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w : ℂ, ‖w‖ ≤ b → w ∉ ball 0 (20 * Real.sqrt ε) →
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, t₀ ≤ t →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_eventually_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_uniform_pole_neighborhood_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα₀
      Ω P hC hcirc μ hGFF hμ] with ω hcross hpoles
  intro b t₀ hb ht₀
  let b' : ℝ := (b + 1) / 2
  have hbb' : b < b' := by dsimp [b']; linarith
  have hb' : b' < 1 := by dsimp [b']; linarith
  obtain ⟨δ, hδ, hδsub⟩ := hpoles b' t₀ hb' ht₀
  have hη : 0 < min (δ / 4) ((b' - b) / 2) :=
    lt_min (by positivity) (by positivity)
  have hsmall : 0 < (min (δ / 4) ((b' - b) / 2)) ^ 2 := sq_pos_of_pos hη
  filter_upwards [hcross, (eventually_lt_nhds hsmall).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hcross hε hεpos
  change 0 < ε at hεpos
  have hsqrt : Real.sqrt ε < min (δ / 4) ((b' - b) / 2) := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hε
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hη] using hs
  have hsδ : Real.sqrt ε < δ / 4 := hsqrt.trans_le (min_le_left _ _)
  have hsb : Real.sqrt ε < (b' - b) / 2 := hsqrt.trans_le (min_le_right _ _)
  intro w hw hw0
  have hw1 : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hw.trans_lt hb)
  obtain ⟨ρ, hρ, hρbound⟩ := hcross w ⟨hw1, hw0⟩
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  have hboundary : dist w 0 + 2 * ρ < 1 := by
    rw [dist_zero_right]
    linarith [hρ.2]
  refine ⟨ρ, hρ, ?_⟩
  intro z t htt
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · by_cases hpole : 2 * ρ < dist z w
    · exact hρbound z hz t (ht₀.trans_le htt) hboundary hpole
    · have hdist : dist w z ≤ 2 * ρ := by simpa [dist_comm] using le_of_not_gt hpole
      have hzsmall : ‖z‖ ≤ b' := by
        have htriangle := dist_triangle z w (0 : ℂ)
        rw [dist_zero_right, dist_zero_right, dist_comm z w] at htriangle
        linarith [hρ.2]
      have hsub : ball w (2 * ρ) ⊆ cluster (μ ω) 1 z t := by
        apply (ball_subset_ball' ?_).trans (hδsub z hzsmall t htt)
        linarith [hρ.2]
      rw [inter_eq_right.mpr hsub]
      exact (IsPreconnected.encard_crossingComponents_le_one
        (isConnected_ball (show 0 < 2 * ρ by positivity)).isPreconnected w _ _).trans
        (by exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1)))
  · rw [cluster_eq_empty_of_pole_not_mem hz (ht₀.trans_le htt).le]
    have hempty : crossingComponents ((∅ : Set ℂ) ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨x, hx, _⟩ := hC.1
      exact hx.1
    rw [hempty]
    simp

end HarmonicBalls

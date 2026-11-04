import HarmonicBalls.Proofs.Sec10.SmallMassCrossings

/-!
# Small-mass crossings on compact subdiscs

The small-mass crossing estimate holds on every fixed subdisc of the half-disc.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- At each scale, sufficiently small mass controls all poles and all crossing
centers in a fixed subdisc of the half-disc, away from the origin. -/
theorem ae_compact_half_disc_crossings_for_small_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b : ℝ, b < 1 / 2 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ T : ℝ, 0 < T ∧
      ∀ w ∈ ball (0 : ℂ) b \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t ∈ Ioc (0 : ℝ) T,
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hcross⟩ := ae_eventually_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hcross α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_small_mass_crossings_eq_empty_all_scales h71 γ α₀ hγ hγ2 hα₀
      Ω P hC hcirc μ hGFF hμ] with ω hcross hsmall
  intro b hb
  have hmargin : 0 < ((1 / 2 : ℝ) - b) / 4 := by linarith
  filter_upwards [hcross, (eventually_lt_nhds (sq_pos_of_pos hmargin)).filter_mono
      nhdsWithin_le_nhds, (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hcross hε hεpos
  change 0 < ε at hεpos
  have hsqrt : Real.sqrt ε < ((1 / 2 : ℝ) - b) / 4 := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hε
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hmargin] at hs
    exact hs
  obtain ⟨T, hT, hTbound⟩ := hsmall ε hεpos
  refine ⟨T, hT, ?_⟩
  intro w hw
  have hw1 : w ∈ ball (0 : ℂ) 1 := (ball_subset_ball (by linarith)) hw.1
  obtain ⟨ρ, hρ, hρbound⟩ := hcross w ⟨hw1, hw.2⟩
  have hwsmall : dist w 0 < b := mem_ball.mp hw.1
  have hboundary : dist w 0 + 2 * ρ < 1 := by linarith [hρ.2]
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht
  by_cases hz : z ∈ ball (0 : ℂ) (1 / 2)
  · rw [hTbound t ht z hz w ρ hρ.1]
    simp
  · by_cases hz1 : z ∈ ball (0 : ℂ) 1
    · have hzfar : (1 / 2 : ℝ) ≤ dist z 0 := by
        exact le_of_not_gt (fun h => hz (mem_ball.mpr h))
      have hzw : 2 * ρ < dist z w := by
        have htri := dist_triangle z w (0 : ℂ)
        linarith [hρ.2]
      exact hρbound z hz1 t ht.1 hboundary hzw
    · rw [cluster_eq_empty_of_pole_not_mem hz1 ht.1.le]
      have hempty : crossingComponents ((∅ : Set ℂ) ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro C hC
        obtain ⟨x, hx, _⟩ := hC.1
        exact hx.1
      rw [hempty]
      simp


end HarmonicBalls

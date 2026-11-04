import HarmonicBalls.Proofs.Sec10.CompactCenterCrossings

/-!
# Crossing centers near the boundary

For clusters contained in a fixed compact subdisc, small crossing balls near
the unit-circle boundary miss the cluster. Together with the compact-center
estimate this removes the boundary restriction on crossing centers, uniformly
above a fixed positive mass.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- With a fixed containment margin and a positive mass lower bound, the
crossing estimate holds at all admissible centers in the unit disk. -/
theorem ae_contained_cluster_crossings_above_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b t₀ : ℝ, b < 1 → 0 < t₀ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, t₀ ≤ t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 b →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_compact_centers_crossings_above_mass hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound
  intro b t₀ hb ht₀
  let b' : ℝ := (b + 1) / 2
  have hbb' : b < b' := by dsimp [b']; linarith
  have hb' : b' < 1 := by dsimp [b']; linarith
  have hη : 0 < min (1 : ℝ) ((b' - b) / 4) := lt_min (by norm_num) (by positivity)
  filter_upwards [hbound b' t₀ hb' ht₀,
    (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε hεpos
  change 0 < ε at hεpos
  have hε1 : ε < 1 := hε.trans_le (min_le_left _ _)
  have hεmargin : ε < (b' - b) / 4 := hε.trans_le (min_le_right _ _)
  have hεsqrt : ε ≤ Real.sqrt ε := by
    have hs := Real.sq_sqrt hεpos.le
    have hn := Real.sqrt_nonneg ε
    nlinarith
  intro w hw
  by_cases hw' : ‖w‖ ≤ b'
  · obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw' hw.2
    exact ⟨ρ, hρ, fun z t ht _ => hρbound z t ht⟩
  · refine ⟨ε, ⟨le_rfl, hεsqrt⟩, ?_⟩
    intro z t ht hcl
    have hempty : cluster (μ ω) 1 z t ∩ ball w (2 * ε) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxsmall : ‖x‖ < b := mem_ball_zero_iff.mp (hcl (subset_closure hx.1))
      have hxw : dist x w < 2 * ε := mem_ball.mp hx.2
      have htriangle := dist_triangle w x (0 : ℂ)
      rw [dist_zero_right, dist_zero_right, dist_comm w x] at htriangle
      have hwb : b' < ‖w‖ := lt_of_not_ge hw'
      linarith
    rw [hempty]
    simp [crossingComponents, connectedComponentsIn]

end HarmonicBalls

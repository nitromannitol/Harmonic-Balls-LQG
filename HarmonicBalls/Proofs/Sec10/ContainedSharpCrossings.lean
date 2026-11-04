import HarmonicBalls.Proofs.Sec10.SharpLocalizationMargins

/-!
# Boundary localization for contained clusters

A fixed containment margin eliminates the boundary restriction in the
crossing estimate. Only centers in a smaller subdisc require pole separation.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- For clusters in a fixed subdisc, the sharp localized crossing bound holds
at all admissible centers and all positive masses. Pole separation is only
needed for centers in the intermediate subdisc. -/
theorem ae_contained_crossings_with_pole_margin
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b : ℝ, b < 1 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 b →
        (‖w‖ ≤ (b + 1) / 2 → ρ + ρ / 50 < dist z w) →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_eventually_crossings_with_sharp_margins hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound
  intro b hb
  let b' : ℝ := (b + 1) / 2
  have hbb' : b < b' := by dsimp [b']; linarith
  have hb' : b' < 1 := by dsimp [b']; linarith
  let η : ℝ := min ((1 - b') / 4) ((b' - b) / 4)
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [hbound, (eventually_lt_nhds (sq_pos_of_pos hη)).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε hεpos
  have hsqrt : Real.sqrt ε < η := by
    have hs := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ ε from hεpos.le) hε
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hη] using hs
  have hηb : η ≤ (1 - b') / 4 := min_le_left _ _
  have hηgap : η ≤ (b' - b) / 4 := min_le_right _ _
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  refine ⟨ρ, hρ, ?_⟩
  intro z hz t ht hcl hpole
  by_cases hw' : ‖w‖ ≤ b'
  · apply hρbound z hz t ht ?_ (hpole hw')
    rw [dist_zero_right]
    linarith [hρ.2]
  · have hempty : cluster (μ ω) 1 z t ∩ ball w (2 * ρ) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxsmall : ‖x‖ < b := mem_ball_zero_iff.mp (hcl (subset_closure hx.1))
      have hxw : dist x w < 2 * ρ := mem_ball.mp hx.2
      have htriangle := dist_triangle w x (0 : ℂ)
      rw [dist_zero_right, dist_zero_right, dist_comm w x] at htriangle
      have hwb : b' < ‖w‖ := lt_of_not_ge hw'
      linarith [hρ.2]
    rw [hempty]
    simp [crossingComponents, connectedComponentsIn]

end HarmonicBalls

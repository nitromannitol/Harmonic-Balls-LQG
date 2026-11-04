import HarmonicBalls.Proofs.Sec10.ExactRadiusSelection

/-!
# Interior crossing bounds with the exact radius interval

For fixed distinct interior points, sufficiently small scales automatically
satisfy the domain and pole margins in the localized crossing estimate.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Away from the origin and the pole, the localized crossing estimate holds
at every sufficiently small scale, uniformly over positive cluster masses. -/
theorem ae_interior_localized_crossings_exact_radius
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ w ∈ ball (0 : ℂ) 1, w ≠ 0 →
      ∀ z ∈ ball (0 : ℂ) 1, z ≠ w → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hcross⟩ := ae_eventually_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hcross α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  intro w hw hw0 z hz hzw
  have hwpos : 0 < dist w 0 := dist_pos.mpr hw0
  have hwunit : dist w 0 < 1 := mem_ball.mp hw
  have hzwpos : 0 < dist z w := dist_pos.mpr hzw
  let η : ℝ := min (dist w 0 / 40) (min ((1 - dist w 0) / 4) (dist z w / 4))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηw : η ≤ dist w 0 / 40 := min_le_left _ _
  have hηb : η ≤ (1 - dist w 0) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηz : η ≤ dist z w / 4 := (min_le_right _ _).trans (min_le_right _ _)
  filter_upwards [hω, (eventually_lt_nhds (sq_pos_of_pos hη)).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hsmall hεpos
  have hsqrt : Real.sqrt ε < η := by
    have hs := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ ε from hεpos.le) hsmall
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hη] using hs
  have hwaway : w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε) := by
    refine ⟨hw, ?_⟩
    rw [mem_ball, not_lt]
    linarith
  obtain ⟨ρ, hρ, hbound⟩ := hε w hwaway
  refine ⟨ρ, hρ, fun t ht => hbound z hz t ht ?_ ?_⟩
  · linarith [hρ.2]
  · linarith [hρ.2]

end HarmonicBalls

import HarmonicBalls.Proofs.Sec10.CrossingPrevalence
import HarmonicBalls.Proofs.Sec7.LatticeApproximation
import HarmonicBalls.Proofs.Sec7.DyadicInterpolation

/-!
# Localized crossing bounds at all small scales

Dyadic interpolation and the planar lattice approximation extend the good-ball
crossing bound to every sufficiently small scale and every permitted centre.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6

universe u

/-- An all-scales form of the localized crossing bound. The lower endpoint is
`ε / 2`, reflecting interpolation between successive dyadic scales; the
boundary and pole margins are retained explicitly. -/
theorem ae_eventually_localized_crossings
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α : ℝ, 0 < α ∧
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc (ε / 2) (Real.sqrt ε),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
          dist w 0 + 2 * ρ < 1 → 2 * ρ < dist z w →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hdyadic⟩ := ae_eventually_dyadic_localized_crossings hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hdyadic α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  rw [eventually_atTop] at hω
  obtain ⟨N, hN⟩ := hω
  have hbound : 0 < min 1 (((2 : ℝ)⁻¹) ^ N) := by positivity
  filter_upwards [(eventually_lt_nhds hbound).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hsmall hε
  change 0 < ε at hε
  have hε1 : ε < 1 := hsmall.trans_le (min_le_left _ _)
  have hεN : ε / 2 < ((2 : ℝ)⁻¹) ^ N := by
    have := hsmall.trans_le (min_le_right (1 : ℝ) (((2 : ℝ)⁻¹) ^ N))
    linarith
  obtain ⟨n, hnN, hnlo, hnhi⟩ := exists_late_dyadic_scale N (half_pos hε) hεN
  let δ : ℝ := ((2 : ℝ)⁻¹) ^ n
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; linarith
  have hsqrt : Real.sqrt δ ≤ Real.sqrt ε := Real.sqrt_le_sqrt hδε.le
  have hεsqrt : ε ≤ Real.sqrt ε := by
    have hs := Real.sq_sqrt hε.le
    have hsn := Real.sqrt_nonneg ε
    nlinarith
  intro w hw
  have haw : 10 * Real.sqrt δ + δ ≤ dist w 0 := by
    have hw' : 20 * Real.sqrt ε ≤ dist w 0 := by
      simpa [mem_ball, not_lt] using hw.2
    linarith
  obtain ⟨x₀, hx₀, hnear⟩ := exists_prevalenceGrid_dist_lt hδpos hw.1 haw
  obtain ⟨ρ, hρ, hcross⟩ := hN n hnN x₀ hx₀
  refine ⟨ρ, ⟨hnlo.trans hρ.1, hρ.2.trans hsqrt⟩, ?_⟩
  have hδρ : δ ≤ ρ := hρ.1
  have hnear' : dist w x₀ < ρ / 6 := by linarith
  intro z hz t ht hboundary hpole
  exact hcross z hz t ht w hnear' hboundary hpole

end HarmonicBalls

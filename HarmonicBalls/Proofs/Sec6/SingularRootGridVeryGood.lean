import HarmonicBalls.Proofs.Sec6.SingularPrescribedGridCommonParameters
import HarmonicBalls.Proofs.Sec6.SimultaneousPrevalenceZeroExistence
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Very-good prevalence at prescribed grid points near singular roots

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- At each prescribed physical scale, a prescribed-grid point near a
singular-mass-typical root has both a shared seven-adic good-annulus count
and an eight-adic very-good count. The thresholds and radius scales in the
two estimates are kept separate, as is the scale-dependent displacement. -/
theorem exists_ae_singular_root_prescribedGrid_good_and_veryGood
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α θ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hθ : (2 + γ)^2 / 2 < θ) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a₇ ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧
    ∃ C : ℕ → ℝ, (∀ i, 1 ≤ C i) ∧
    ∃ c C₃ a₈ C₁m C₁p C₂m C₂p : ℝ,
      0 < c ∧ 0 < C₃ ∧ a₈ ∈ Ioo (0 : ℝ) 1 ∧
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
      ∀ i, ∀ᶠ n : ℕ in atTop,
        ∃ z ∈ prevalenceGrid (dyadicScale n),
          dist w z < δ * (s i * (C i * dyadicScale n)) ∧
          (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n * s i) (Real.sqrt (dyadicScale n) * s i) ∧
              (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z ((a₇/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b ∧
              IsGoodAnnulus (μ ω) r w ((a₇/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ) ∧
          c * Real.logb 8 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({ρ : ℝ | ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, ρ = (8 : ℝ)⁻¹ ^ k) ∧
              IsVeryGoodAnnulus (μ ω) θ ρ z N₀ a₈ b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ) := by
  obtain ⟨a₇, ha₇, δ, hδ, C, hC', hseven⟩ :=
    exists_ae_singular_mass_prescribedGrid_common_parameters
      hball h hμ hμ₀ hAff hCC hγ hγ2 hα hb.1 β hβ s hs
  obtain ⟨c, C₃, a₈, C₁m, C₁p, C₂m, C₂p, hc, hC₃, ha₈, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, height⟩ := veryGoodAnnuli_prevalence_all_singularities_of_zero_existence
      (veryGoodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth)
      P γ θ hγ hγ2 hθ hC hcirc h hE₀ hb (abs_nonneg α)
  refine ⟨a₇, ha₇, δ, hδ, C, hC', c, C₃, a₈, C₁m, C₁p, C₂m, C₂p,
    hc, hC₃, ha₈, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  have he : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ z ∈ prevalenceGrid (dyadicScale n),
      c * Real.logb 8 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
          (∃ k : ℕ, ρ = (8 : ℝ)⁻¹ ^ k) ∧
          IsVeryGoodAnnulus (μ ω) θ ρ z N₀ a₈ b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ) := by
    filter_upwards [(height N₀ le_rfl).ae_eventually_dyadic, hμ] with ω hω hμω
    filter_upwards [hω] with n hn z hz
    exact hn α le_rfl (μ ω) hμω z hz
  filter_upwards [hseven, he] with ω hsevenω heω
  filter_upwards [hsevenω] with w hw
  intro i
  filter_upwards [hw i, heω] with n hn hgrid
  obtain ⟨z, hz, hd, hgood⟩ := hn
  exact ⟨z, hz, hd, hgood, hgrid z hz⟩

end HarmonicBalls.Section6

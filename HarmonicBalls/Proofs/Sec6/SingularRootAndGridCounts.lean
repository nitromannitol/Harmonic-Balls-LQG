import HarmonicBalls.Proofs.Sec6.SingularMassTypicalDyadicAnnuli
import HarmonicBalls.Proofs.Sec6.SimultaneousPrevalenceZeroExistence
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Singular-root and prevalence-grid counts

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- For almost every field and singular-mass-typical root, both the
prescribed prevalence-grid count and the root count hold eventually on
dyadic windows. The two counts use their own thresholds and scale windows. -/
theorem exists_ae_singular_root_and_grid_eventually_dyadic_counts
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ c a₁ a₂ : ℝ, 0 < c ∧ a₁ ∈ Ioo (0 : ℝ) 1 ∧ a₂ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball 0 1),
        (∀ᶠ n : ℕ in atTop, ∀ y ∈ prevalenceGrid (dyadicScale n),
          c * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r y a₁ b}.ncard : ℝ)) ∧
        (∀ i, ∀ᶠ n : ℕ in atTop,
          (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
            (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ ω) (s i * r) z
              (a₂ / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ)) := by
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_ballMass hball
  obtain ⟨c, a₁, hc, ha₁, hgrid⟩ :=
    goodAnnuli_prevalence_all_singularities_of_zero_existence
      (goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth)
      P γ hγ hγ2 hC hcirc h hE₀ hb (abs_nonneg α)
  obtain ⟨a₂, ha₂, hroot⟩ :=
    exists_ae_singular_mass_eventually_dyadic_goodAnnuli_count_of_existence
      hball hγ hγ2 hα h hμ hE₀ hb.1 β hβ s hs
  refine ⟨c, a₁, a₂, hc, ha₁, ha₂, ?_⟩
  filter_upwards [hgrid.ae_eventually_dyadic, hroot, hμ] with ω hg hr hlim
  filter_upwards [hr] with z hz
  refine ⟨?_, hz⟩
  filter_upwards [hg] with n hn
  exact hn α le_rfl (μ ω) hlim

end HarmonicBalls.Section6

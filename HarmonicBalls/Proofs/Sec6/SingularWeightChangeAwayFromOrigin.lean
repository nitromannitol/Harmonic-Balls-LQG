import HarmonicBalls.Proofs.Sec6.SimultaneousPrevalenceZeroExistence
import HarmonicBalls.Proofs.Sec6.SingularWeightChange

/-! # Change of logarithmic singularity away from the origin

The imported Section 6 annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Zero-strength existence
is a staged literature input pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal

universe u

/-- For every pair of existing limits, changing the logarithmic singularity
weights the restriction away from the origin by a power of distance. -/
theorem ae_existing_limits_change_singularity_away_zero_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν →
      μ.restrict {0}ᶜ = (ν.restrict {0}ᶜ).withDensity
        (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))) := by
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc hG hE0
  filter_upwards [hrepr] with ω hrepr α β μ ν hμ hν
  let base := (μ₀ ω).restrict ({0} : Set ℂ)ᶜ
  have hzero : base {0} = 0 := by
    simp [base]
  have hrepr' (a : ℝ) (m : Measure ℂ)
      (hm : IsLQGLimit γ (fieldCircleAverage a (hcirc ω)) m) :
      m.restrict {0}ᶜ = base.withDensity
        (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * a)))) := by
    dsimp only [base]
    rw [← restrict_withDensity (measurableSet_singleton 0).compl]
    exact hrepr a m hm
  rw [hrepr' α μ hμ, hrepr' β ν hν,
    withDensity_norm_rpow_withDensity base hzero]
  congr 2
  ring

/-- Every pair of existing logarithmically singular limits is mutually
absolutely continuous away from the origin, on one common full-measure event. -/
theorem ae_existing_limits_mutually_absolutelyContinuous_away_zero_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν →
      μ.restrict {0}ᶜ ≪ ν.restrict {0}ᶜ ∧
        ν.restrict {0}ᶜ ≪ μ.restrict {0}ᶜ := by
  filter_upwards [ae_existing_limits_change_singularity_away_zero_of_zero_existence
    P γ hγ hγ2 hC hcirc hG hE0] with ω hchange α β μ ν hμ hν
  constructor
  · rw [hchange α β μ ν hμ hν]
    exact withDensity_absolutelyContinuous _ _
  · rw [hchange β α ν μ hν hμ]
    exact withDensity_absolutelyContinuous _ _

/-- Increasing the singularity strength increases the measure inside the
unit disc and decreases it outside, after restriction away from the origin. -/
theorem ae_existing_limits_monotone_away_zero_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, α ≤ β → ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν →
      (μ.restrict {0}ᶜ).restrict (Metric.closedBall 0 1) ≤
        (ν.restrict {0}ᶜ).restrict (Metric.closedBall 0 1) ∧
      (ν.restrict {0}ᶜ).restrict (Metric.closedBall 0 1)ᶜ ≤
        (μ.restrict {0}ᶜ).restrict (Metric.closedBall 0 1)ᶜ := by
  filter_upwards [ae_existing_limits_change_singularity_away_zero_of_zero_existence
    P γ hγ hγ2 hC hcirc hG hE0] with ω hchange α β hαβ μ ν hμ hν
  rw [hchange α β μ ν hμ hν]
  exact restrict_withDensity_norm_rpow_compare (ν.restrict {0}ᶜ)
    (mul_nonneg hγ.le (sub_nonneg.mpr hαβ))

end HarmonicBalls.Section6

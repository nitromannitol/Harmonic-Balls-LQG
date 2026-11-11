import HarmonicBalls.Proofs.Sec6.SingularWeightChangeAwayFromOrigin

/-! # Negative logarithmic singularities from zero-strength existence

The imported Section 6 annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Zero-strength existence
is a literature input (PENDING TRUTH CHECK).
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal

universe u

/-- On a common event, every existing limit with negative singularity has no
atom at the origin. No existence input at the negative strength is needed. -/
theorem ae_existing_negative_limits_origin_nonatomic_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, α < 0 → ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ → μ {0} = 0 := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE0 hG hγ hγ2 hQ
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [hμ₀, hc0] with ω hμ₀ hc0 α hα μ hμ
  exact origin_nonatomic_of_stronger_singularity hγ hα (hcirc ω) μ (μ₀ ω) hμ hμ₀ hc0

/-- Every existing negative-singularity limit is determined on the whole
plane by a single zero-strength limit on a common full-measure event. -/
theorem exists_ae_existing_negative_limits_eq_singularWeight_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, α < 0 → ∀ μ : Measure ℂ,
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        μ = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc hG hE0
  refine ⟨μ₀, hμ₀, ?_⟩
  filter_upwards [hrepr, ae_existing_negative_limits_origin_nonatomic_of_zero_existence
    P γ hγ hγ2 hC hcirc hG hE0] with ω hrepr hno α hα μ hμ
  have hweightzero : ((μ₀ ω).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))) {0} = 0 := by
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    simp [Real.zero_rpow (by nlinarith : -(γ * α) ≠ 0)]
  have hm_ae : ∀ᵐ z ∂μ, z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hno α hα μ hμ
  have hw_ae : ∀ᵐ z ∂((μ₀ ω).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))), z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hweightzero
  have h := hrepr α μ hμ
  rw [Measure.restrict_eq_self_of_ae_mem hm_ae, Measure.restrict_eq_self_of_ae_mem hw_ae] at h
  exact h

/-- Existing negative-singularity limits are mutually absolutely continuous
on the whole plane, simultaneously for all negative strengths. -/
theorem ae_existing_negative_limits_mutually_absolutelyContinuous_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, α < 0 → β < 0 → ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν → μ ≪ ν ∧ ν ≪ μ := by
  filter_upwards [ae_existing_limits_mutually_absolutelyContinuous_away_zero_of_zero_existence
      P γ hγ hγ2 hC hcirc hG hE0,
    ae_existing_negative_limits_origin_nonatomic_of_zero_existence
      P γ hγ hγ2 hC hcirc hG hE0] with ω hac hno α β hα hβ μ ν hμ hν
  have hm : ∀ᵐ z ∂μ, z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hno α hα μ hμ
  have hn : ∀ᵐ z ∂ν, z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hno β hβ ν hν
  have h := hac α β μ ν hμ hν
  rw [Measure.restrict_eq_self_of_ae_mem hm, Measure.restrict_eq_self_of_ae_mem hn] at h
  exact h

end HarmonicBalls.Section6

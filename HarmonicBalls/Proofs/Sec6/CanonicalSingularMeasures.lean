import HarmonicBalls.Proofs.Sec6.WeakerSingularityExistence
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure

/-! # Canonical subcritical singular LQG measures

The Section 6 assemblies imported here use Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The existence assumptions
below are staged literature inputs pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal Topology

universe u

/-- A cofinal family of subcritical existence inputs determines one
whole-plane measure which represents every subcritical limit on a common
full-measure event. No whole-plane ball-mass estimate is used. -/
theorem exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ → ∀ μ : Measure ℂ,
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
          μ = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistence_of_cofinal P γ 0 hC hcirc hE hG hγ hγ2 hQ
  refine ⟨μ₀, hμ₀, ?_⟩
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc hG hE,
      hμ₀, hc0] with ω hzero hm₀ hc₀ α hα μ hm
  have hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
        ((μ₀ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
    fun f hf => isLQGLimit_addCircleAverage hm₀ hc₀ f hf
  exact eq_singularWeight_of_origin_nonatomic hm hW (hzero α hα μ hm) (hzero 0 hQ (μ₀ ω) hm₀)

/-- All subcritical measures are simultaneously obtained by singular Weyl
weighting one whole-plane limit. This includes existence and uniqueness of
the limit for each subcritical strength. -/
theorem exists_ae_canonical_subcritical_lqgMeasures
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω))
          ((μ₀ ω).withDensity fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) ∧
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
          μ = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal P γ hγ hγ2 hC hcirc hG hE
  refine ⟨μ₀, hμ₀, ?_⟩
  filter_upwards [hrepr, ae_exists_lqgLimit_for_all_subcritical P γ hγ hγ2 hC hcirc hG hE]
    with ω hrepr hex α hα
  obtain ⟨μ, hμ⟩ := hex α hα
  refine ⟨?_, hrepr α hα⟩
  rw [← hrepr α hα μ hμ]
  exact hμ

/-- On a common full-measure event all subcritical LQG limits are mutually
absolutely continuous. This follows from cofinal existence, without a
whole-plane ball-mass bound. -/
theorem ae_subcritical_limits_mutually_absolutelyContinuous_of_cofinal
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, α < lqgQ γ → β < lqgQ γ → ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν → μ ≪ ν ∧ ν ≪ μ := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal P γ hγ hγ2 hC hcirc hG hE
  filter_upwards [hrepr, hμ₀,
      ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc hG hE]
    with ω hrepr hm₀ hzero α β hα hβ μ ν hμ hν
  rw [hrepr α hα μ hμ, hrepr β hβ ν hν]
  have hno := hzero 0 hQ (μ₀ ω) hm₀
  constructor
  · exact (withDensity_absolutelyContinuous (μ₀ ω) _).trans
      (absolutelyContinuous_singularWeight hno _)
  · exact (withDensity_absolutelyContinuous (μ₀ ω) _).trans
      (absolutelyContinuous_singularWeight hno _)

/-- If the base measure has no atom at the origin, the singularly weighted
measure is a measurable function of the singularity strength. -/
theorem measurable_singularWeight_parameter (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hzero : μ {0} = 0) (γ : ℝ) :
    Measurable (fun α : ℝ => μ.withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))) := by
  have hf : Measurable (fun p : ℝ × ℂ =>
      ENNReal.ofReal (Real.exp (-(γ * p.1) * Real.log ‖p.2‖))) := by
    exact ((measurable_const.mul measurable_fst).neg.mul
      (Real.measurable_log.comp measurable_snd.norm)).exp.ennreal_ofReal
  have hm : Measurable (fun α : ℝ => μ.withDensity
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log ‖z‖)))) :=
    measurable_withDensity hf
  convert hm using 1
  funext α
  apply withDensity_congr_ae
  have hne : ∀ᵐ z ∂μ, z ≠ (0 : ℂ) := by simpa [ae_iff] using hzero
  filter_upwards [hne] with z hz
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
  congr 2
  ring

/-- The canonical family exists simultaneously and is measurable in the
singularity strength on a common full-measure event. -/
theorem exists_ae_measurable_canonical_subcritical_lqgMeasures
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P,
        Measurable (fun α : ℝ => (μ₀ ω).withDensity
          (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))) ∧
        ∀ α : ℝ, α < lqgQ γ → IsLQGLimit γ (fieldCircleAverage α (hcirc ω))
          ((μ₀ ω).withDensity fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀, hcanonical⟩ :=
    exists_ae_canonical_subcritical_lqgMeasures P γ hγ hγ2 hC hcirc hG hE
  refine ⟨μ₀, hμ₀, ?_⟩
  filter_upwards [hμ₀, hcanonical,
      ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc hG hE]
    with ω hm₀ hcanonical hzero
  let : IsLocallyFiniteMeasure (μ₀ ω) := hm₀.isLocallyFiniteMeasure
  exact ⟨measurable_singularWeight_parameter (μ₀ ω) (hzero 0 hQ (μ₀ ω) hm₀) γ,
    fun α hα => (hcanonical α hα).1⟩

end HarmonicBalls.Section6

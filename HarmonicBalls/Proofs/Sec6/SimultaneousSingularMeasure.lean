import HarmonicBalls.Proofs.Sec6.Section6FromCofinalExistence

/-! # Simultaneous characterization of singular LQG measures

The Section 6 assembly imported here uses Leonardo Bonanno's Gwynne–Miller
lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The existence
assumptions below are staged literature inputs pending source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

universe u

/-- If the singular and whole-plane limits have no atom at the origin, the
local Weyl identity extends to an identity of measures on the whole plane. -/
theorem eq_singularWeight_of_origin_nonatomic
    {γ α : ℝ} {hc : ℝ → ℂ → ℝ} {μ μ₀ : Measure ℂ}
    (hm : IsLQGLimit γ (fieldCircleAverage α hc) μ)
    (hW : ∀ f : ℂ → ℝ, Continuous f → IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 hc) f)
      (μ₀.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))))
    (hzero : μ {0} = 0) (hzero₀ : μ₀ {0} = 0) :
    μ = μ₀.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  have hwzero : (μ₀.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))) {0} = 0 :=
    (withDensity_absolutelyContinuous μ₀ _) hzero₀
  have hm_ae : ∀ᵐ z ∂μ, z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hzero
  have hw_ae : ∀ᵐ z ∂(μ₀.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))),
      z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hwzero
  have h := restrict_compl_zero_eq_withDensity hm hW
  rw [Measure.restrict_eq_self_of_ae_mem hm_ae, Measure.restrict_eq_self_of_ae_mem hw_ae] at h
  exact h

/-- Given the staged existence input at zero and a countable cofinal family
of singularities, one whole-plane LQG measure characterizes every subcritical
limit on a common full-measure event. The statement makes no assertion that a
limit exists for each strength. -/
theorem exists_ae_all_subcritical_limits_eq_singularWeight
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ → ∀ μ : Measure ℂ,
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
          μ = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE0 hG hγ hγ2 hQ
  refine ⟨μ₀, hμ₀, ?_⟩
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc hG hE,
      hμ₀, hc0, ae_wholePlane_nonatomic_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀]
    with ω hzero hm₀ hc₀ hno α hα μ hm
  have hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
        ((μ₀ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
    fun f hf => isLQGLimit_addCircleAverage hm₀ hc₀ f hf
  exact eq_singularWeight_of_origin_nonatomic hm hW (hzero α hα μ hm) (hno 0)

/-- The singular weight preserves the null sets of any measure which has no
atom at the origin. -/
theorem absolutelyContinuous_singularWeight {μ : Measure ℂ} (hzero : μ {0} = 0)
    (a : ℝ) : μ ≪ μ.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ a)) := by
  have hne : ∀ᵐ z ∂μ, z ≠ (0 : ℂ) := by simpa [ae_iff] using hzero
  have heq : μ.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ a)) =
      μ.withDensity (fun z => ENNReal.ofReal (Real.exp (a * Real.log ‖z‖))) := by
    apply withDensity_congr_ae
    filter_upwards [hne] with z hz
    rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
    congr 2
    ring
  rw [heq]
  apply withDensity_absolutelyContinuous'
    ((Real.measurable_exp.comp ((Real.measurable_log.comp measurable_norm).const_mul a)).ennreal_ofReal.aemeasurable)
  filter_upwards [] with z
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))

/-- On one full-measure event, all existing subcritical LQG limits formed
from these circle averages are mutually absolutely continuous, even for
uncountably many singularity strengths. -/
theorem ae_all_subcritical_limits_mutually_absolutelyContinuous
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, α < lqgQ γ → β < lqgQ γ → ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν → μ ≪ ν ∧ ν ≪ μ := by
  obtain ⟨μ₀, hμ₀, h⟩ := exists_ae_all_subcritical_limits_eq_singularWeight
    hS P γ hγ hγ2 hC hcirc hG hE0 hE
  filter_upwards [h, ae_wholePlane_nonatomic_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀]
    with ω hω hno α β hα hβ μ ν hμ hν
  rw [hω α hα μ hμ, hω β hβ ν hν]
  constructor
  · exact (withDensity_absolutelyContinuous (μ₀ ω) _).trans
      (absolutelyContinuous_singularWeight (hno 0) _)
  · exact (withDensity_absolutelyContinuous (μ₀ ω) _).trans
      (absolutelyContinuous_singularWeight (hno 0) _)

/-- The lower whole-plane multiscale mass bound gives full support. -/
theorem ae_wholePlane_fullSupport_of_scaledBallMass
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U := by
  let β : ℝ := (2 - γ) ^ 2 / 4
  let βm : ℝ := (2 + γ) ^ 2 / 2 + 1
  let ζ : ℝ := 1 / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβlt : β < (2 - γ) ^ 2 / 2 := by
    dsimp [β]; nlinarith [sq_pos_of_pos (show 0 < 2 - γ by linarith)]
  have key (n : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ closedBall (0 : ℂ) ((n : ℝ) + 1),
        0 < μ ω (ball z ((2 : ℝ)⁻¹ ^ k)) := by
    have hpoly := hS γ hγ hγ2 Ω P hC hcirc μ hG hμ ((n : ℝ) + 1) (by positivity)
      β βm ζ hβ hβlt (by dsimp [βm]; linarith) (by dsimp [ζ]; norm_num)
      (by dsimp [ζ]; norm_num)
    filter_upwards [hpoly.ae_eventually_dyadic] with ω hω
    filter_upwards [hω] with k hk z hz
    have hδ : 0 < ((2 : ℝ)⁻¹ ^ k) := by positivity
    have hδ1 : ((2 : ℝ)⁻¹ ^ k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hrad : ((2 : ℝ)⁻¹ ^ k) ^ (1 - ζ) ≤ 1 :=
      Real.rpow_le_one hδ.le hδ1 (by dsimp [ζ]; norm_num)
    have hbound := (hk 1 hrad le_rfl z (by simpa using hz)).1
    simp only [Real.one_rpow, one_mul, div_one] at hbound
    exact (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hbound
  have hscale : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [ae_all_iff.mpr key] with ω hω U hU hne
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  have hzn : z ∈ closedBall (0 : ℂ) ((n : ℝ) + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨k, hk, hkr⟩ := ((hω n).and (hscale.eventually (Iio_mem_nhds hr))).exists
  exact (hk z hzn).trans_le (measure_mono ((ball_subset_ball hkr.le).trans hrU))

/-- On one full-measure event, every existing LQG limit with a logarithmic
singularity has full support. No existence or subcriticality assumption is
needed for the singular limits. -/
theorem ae_fullSupport_all_singular_limits
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE0 hG hγ hγ2 hQ
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [hμ₀, hc0,
      ae_wholePlane_nonatomic_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀,
      ae_wholePlane_fullSupport_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀]
    with ω hm₀ hc₀ hno hfull α μ hm U hU hne
  have hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
        ((μ₀ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
    fun f hf => isLQGLimit_addCircleAverage hm₀ hc₀ f hf
  have hweight := restrict_compl_zero_eq_withDensity hm hW
  let ν := (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))
  have hνzero : ν {0} = 0 := (withDensity_absolutelyContinuous (μ₀ ω) _) (hno 0)
  have hνae : ∀ᵐ z ∂ν, z ∈ ({0} : Set ℂ)ᶜ := by simpa [ae_iff] using hνzero
  have hνrest : ν.restrict ({0} : Set ℂ)ᶜ = ν := Measure.restrict_eq_self_of_ae_mem hνae
  have hAC : μ₀ ω ≪ ν := absolutelyContinuous_singularWeight (hno 0) _
  by_contra hn
  have hμzero : μ U = 0 := le_zero_iff.mp (not_lt.mp hn)
  have hνU : ν U = 0 := by
    rw [← hνrest, ← hweight]
    apply le_zero_iff.mp
    calc (μ.restrict ({0} : Set ℂ)ᶜ) U ≤ μ U := Measure.restrict_le_self U
      _ = 0 := hμzero
  exact (ne_of_gt (hfull U hU hne)) (hAC hνU)

/-- Full support for the frozen Section 2 statement follows from whole-plane
multiscale mass bounds and existence of the whole-plane LQG measure. -/
theorem lqgMeasureFullSupportStmt_of_scaledBallMass_and_existence
    (hS : WholePlaneScaledBallMassStep.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : LQGMeasureFullSupportStmt.{u} := by
  intro γ α hγ hγ2 hα Ω _ P hC hcirc μ hG hμ
  filter_upwards [ae_fullSupport_all_singular_limits hS P γ hγ hγ2 hC hcirc hG
      (hE0 Ω P γ hC hcirc), hμ] with ω hfull hm
  exact hfull α (μ ω) hm

end HarmonicBalls.Section6

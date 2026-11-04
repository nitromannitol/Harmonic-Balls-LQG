import HarmonicBalls.Proofs.Sec6.NegativeSingularityZeroExistence
import HarmonicBalls.Proofs.Sec6.SingularityParameterContinuity

/-! # Existence at nonpositive logarithmic singularities

The imported Section 6 annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Zero-strength existence
is a staged literature input pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal Topology

universe u

/-- A zero-strength limit constructs every nonpositive-strength limit
simultaneously, and each such limit is unique. -/
theorem exists_ae_canonical_nonpositive_limits_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, α ≤ 0 →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω))
          ((μ₀ ω).withDensity fun z => ENNReal.ofReal (‖z‖ ^ (γ * (0 - α)))) ∧
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
          μ = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (0 - α)))) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE0 hG hγ hγ2 hQ
  have hc0 : ∀ᵐ ω ∂P, ∀ n : ℕ,
      Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n))
  refine ⟨μ₀, hμ₀, ?_⟩
  filter_upwards [hμ₀, hc0] with ω hμ₀ hc0 α hα
  have hm := isLQGLimit_of_weaker_singularity hγ.le hα (hcirc ω) hμ₀ hc0
  exact ⟨hm, fun _ h => h.unique hm⟩

/-- A jointly measurable family realizes all nonpositive-strength limits on a
single full-measure event; its test integrals vary continuously below zero. -/
theorem exists_jointly_measurable_vaguely_continuous_nonpositive_limits_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∃ M : Ω × ℝ → Measure ℂ, Measurable M ∧
      ∀ᵐ ω ∂P, (∀ α : ℝ, α ≤ 0 →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α))) ∧
      ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
        ContinuousOn (fun α => ∫ z, φ z ∂(M (ω, α))) (Iio 0) := by
  obtain ⟨μ₀, hμ₀, hcanonical⟩ :=
    exists_ae_canonical_nonpositive_limits_of_zero_existence P γ hγ hγ2 hC hcirc hG hE0
  have hl : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ₀ ω) := by
    filter_upwards [hμ₀] with ω hω
    exact hω.isLocallyFiniteMeasure
  let w : ℝ → ℂ → ℝ≥0∞ := fun α z =>
    if z = 0 then (if α = 0 then 1 else 0) else ENNReal.ofReal (Real.exp ((γ * (0 - α)) * Real.log ‖z‖))
  have hw : Measurable (Function.uncurry w) := by
    apply Measurable.ite (measurableSet_singleton 0 |>.preimage measurable_snd)
      (Measurable.ite (measurableSet_singleton 0 |>.preimage measurable_fst) measurable_const measurable_const)
    exact ((measurable_const.mul (measurable_const.sub measurable_fst)).mul
      (Real.measurable_log.comp measurable_snd.norm)).exp.ennreal_ofReal
  obtain ⟨M, hM, hMeq⟩ := exists_jointly_measurable_weighted_modification P μ₀
    (hG.aemeasurable_lqgMeasure hμ₀) hl w hw
  refine ⟨M, hM, ?_⟩
  filter_upwards [hμ₀, hcanonical, hMeq] with ω hm₀ hcanonical hMeq
  have heq (α : ℝ) (hα : α ≤ 0) : M (ω, α) = (μ₀ ω).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (0 - α)))) := by
    rw [hMeq α]
    by_cases hα0 : α = 0
    · subst α
      congr 1
      funext z
      by_cases hz : z = 0 <;> simp [w, hz]
    have hαlt : α < 0 := lt_of_le_of_ne hα hα0
    congr 1
    funext z
    by_cases hz : z = 0
    · subst z
      have hp : γ * (0 - α) ≠ 0 := ne_of_gt (mul_pos hγ (sub_pos.mpr hαlt))
      simp only [w, ite_eq_left rfl, ite_eq_right hα0, norm_zero, Real.zero_rpow hp, ENNReal.ofReal_zero]
    · simp only [w, ite_eq_right hz]
      rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
      congr 2
      ring
  constructor
  · intro α hα
    rw [heq α hα]
    exact (hcanonical α hα).1
  · intro φ hφ hφc
    let : IsLocallyFiniteMeasure (μ₀ ω) := hm₀.isLocallyFiniteMeasure
    have hcont := continuousOn_integral_weaker_singularity (μ₀ ω) (β := 0) hγ φ hφ hφc
    apply hcont.congr
    intro α hα
    change (∫ z, φ z ∂(M (ω, α))) = _
    rw [heq α hα.le]

end HarmonicBalls.Section6

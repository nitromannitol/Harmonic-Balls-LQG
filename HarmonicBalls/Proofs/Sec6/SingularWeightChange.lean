import HarmonicBalls.Proofs.Sec6.CanonicalSingularMeasures

/-! # Change of logarithmic singularity

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The cofinal existence
hypotheses below are staged literature inputs pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal

/-- A power of distance is almost everywhere measurable when the measure
has no atom at the origin. -/
theorem aemeasurable_ofReal_norm_rpow (μ : Measure ℂ) (hzero : μ {0} = 0) (p : ℝ) :
    AEMeasurable (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ p)) μ := by
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (Real.exp (Real.log ‖z‖ * p))) :=
    (Real.measurable_log.comp measurable_id.norm |>.mul_const p |>.exp).ennreal_ofReal
  apply hm.aemeasurable.congr
  have hne : ∀ᵐ z ∂μ, z ≠ (0 : ℂ) := by simpa [ae_iff] using hzero
  filter_upwards [hne] with z hz
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

/-- Successive power weights add their exponents, provided the original
measure has no atom at the origin. -/
theorem withDensity_norm_rpow_withDensity (μ : Measure ℂ) (hzero : μ {0} = 0)
    (p q : ℝ) :
    (μ.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ p))).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ q)) =
    μ.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (p + q))) := by
  rw [← withDensity_mul₀ (aemeasurable_ofReal_norm_rpow μ hzero p)
    (aemeasurable_ofReal_norm_rpow μ hzero q)]
  apply withDensity_congr_ae
  have hne : ∀ᵐ z ∂μ, z ≠ (0 : ℂ) := by simpa [ae_iff] using hzero
  filter_upwards [hne] with z hz
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg z) p),
    ← Real.rpow_add (norm_pos_iff.mpr hz)]

universe u

/-- On a common full-measure event, changing between any two subcritical
logarithmic singularities weights the measure by the corresponding power
of distance to the origin. -/
theorem ae_subcritical_limits_change_singularity_of_cofinal
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, α < lqgQ γ → β < lqgQ γ → ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν →
      μ = ν.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal P γ hγ hγ2 hC hcirc hG hE
  filter_upwards [hrepr, hμ₀,
      ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc hG hE]
    with ω hrepr hm₀ hzero α β hα hβ μ ν hμ hν
  have hz := hzero 0 hQ (μ₀ ω) hm₀
  rw [hrepr α hα μ hμ, hrepr β hβ ν hν,
    withDensity_norm_rpow_withDensity (μ₀ ω) hz]
  congr 2
  ring

/-- On the unit disc a nonnegative power weight decreases a measure, while
outside the disc it increases the measure. -/
theorem restrict_withDensity_norm_rpow_compare (ν : Measure ℂ) {p : ℝ} (hp : 0 ≤ p) :
    (ν.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ p))).restrict (Metric.closedBall 0 1) ≤
        ν.restrict (Metric.closedBall 0 1) ∧
    ν.restrict (Metric.closedBall 0 1)ᶜ ≤
      (ν.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ p))).restrict (Metric.closedBall 0 1)ᶜ := by
  constructor
  · rw [restrict_withDensity Metric.isClosed_closedBall.measurableSet]
    calc
      _ ≤ (ν.restrict (Metric.closedBall 0 1)).withDensity 1 := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
        have hz' : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
        simpa only [Pi.one_apply, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.rpow_le_one (norm_nonneg z) hz' hp)
      _ = _ := withDensity_one
  · rw [restrict_withDensity Metric.isClosed_closedBall.measurableSet.compl]
    calc
      _ = (ν.restrict (Metric.closedBall 0 1)ᶜ).withDensity 1 := withDensity_one.symm
      _ ≤ _ := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet.compl] with z hz
        have hz' : 1 ≤ ‖z‖ := by
          have : ¬ ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
          exact (lt_of_not_ge this).le
        simpa only [Pi.one_apply, ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (Real.one_le_rpow hz' hp)

/-- Simultaneous monotonicity in the logarithmic singularity strength, with
opposite directions inside and outside the unit disc. -/
theorem ae_subcritical_limits_monotone_on_unit_disc_of_cofinal
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α β : ℝ, α ≤ β → α < lqgQ γ → β < lqgQ γ → ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage β (hcirc ω)) ν →
      μ.restrict (Metric.closedBall 0 1) ≤ ν.restrict (Metric.closedBall 0 1) ∧
      ν.restrict (Metric.closedBall 0 1)ᶜ ≤ μ.restrict (Metric.closedBall 0 1)ᶜ := by
  filter_upwards [ae_subcritical_limits_change_singularity_of_cofinal
    P γ hγ hγ2 hC hcirc hG hE] with ω hchange α β hαβ hα hβ μ ν hμ hν
  rw [hchange α β hα hβ μ ν hμ hν]
  exact restrict_withDensity_norm_rpow_compare ν (mul_nonneg hγ.le (sub_nonneg.mpr hαβ))

end HarmonicBalls.Section6

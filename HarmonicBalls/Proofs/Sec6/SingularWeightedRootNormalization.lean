import HarmonicBalls.Proofs.Sec6.WeightedUnitDiscRootTail
import HarmonicBalls.Proofs.Sec6.WeakerSingularityExistence
import HarmonicBalls.Proofs.Sec6.VolumeGrowthNonatomic
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure

/-! # Normalization for singular LQG root weights

The imported Section 6 results use Leonardo Bonanno's Gwynne–Miller lemma
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Metric
open scoped ENNReal

universe u

/-- For a weaker singularity, the weighted whole-plane measure has positive
finite mass on the unit disc without a separate existence assumption. -/
theorem ae_weaker_singularWeight_unitDisc_mass_pos_ne_top
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ((μ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))))
      (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))))
      (ball 0 1) ≠ ∞ := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => h.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n))
  filter_upwards [hμ, hc, ae_unitDisc_lqg_mass_pos_ne_top hgrowth hγ hγ2 h hμ,
    lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc h hγ hγ2 hQ μ hμ]
    with ω hm hc hmpos hno
  have hlim := isLQGLimit_of_weaker_singularity (le_of_lt hγ) hα (hcirc ω) hm hc
  have heq : γ * (0 - α) = -(γ * α) := by ring
  rw [heq] at hlim
  let : IsLocallyFiniteMeasure ((μ ω).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))) := hlim.isLocallyFiniteMeasure
  exact ⟨fun hz => hmpos.1 (absolutelyContinuous_singularWeight (hno 0) _ hz),
    measure_ball_ne_top⟩

/-- At any subcritical singularity, its staged existence implies positive
finite normalization for the corresponding whole-plane weight. -/
theorem ae_subcritical_singularWeight_unitDisc_mass_pos_ne_top
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hE : LQGMeasureExistence P γ α hC hcirc) :
    ∀ᵐ ω ∂P, ((μ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))))
      (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))))
      (ball 0 1) ≠ ∞ := by
  obtain ⟨ν, hν⟩ := hE h hγ hγ2 hα
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => h.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n))
  filter_upwards [hμ, hν, hc, ae_unitDisc_lqg_mass_pos_ne_top hgrowth hγ hγ2 h hμ,
    lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc h hγ hγ2 hQ μ hμ,
    lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ α hC hcirc h hγ hγ2 hα ν hν]
    with ω hm hn hc hmpos hno hnno
  have heq := eq_singularWeight_of_origin_nonatomic hn
    (fun f hf => isLQGLimit_addCircleAverage hm hc f hf) (hnno 0) (hno 0)
  let : IsLocallyFiniteMeasure (ν ω) := hn.isLocallyFiniteMeasure
  refine ⟨fun hz => hmpos.1 (absolutelyContinuous_singularWeight (hno 0) _ hz), ?_⟩
  rw [← heq]
  exact measure_ball_ne_top

end HarmonicBalls.Section6

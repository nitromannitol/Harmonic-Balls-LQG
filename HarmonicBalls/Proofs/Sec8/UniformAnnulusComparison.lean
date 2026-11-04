import HarmonicBalls.Proofs.Sec8.LQGUniversalMeasureLaw
import HarmonicBalls.Proofs.Sec8.AnnulusRatioScaling

/-! # Model-independent annulus comparison threshold -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- A single reference realization fixes a threshold that works on every
other probability space and at every dyadic scale. -/
theorem exists_uniform_lqg_annulusBallComparison_threshold
    (hfull : LQGMeasureFullSupportStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ) (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ)
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ α₀ hcirc₀ μ₀)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ α₀ hC hcirc →
      ∀ n, P {ω | ¬ AnnulusBallComparison (μ ω) n 0 m} ≤ δ := by
  let : IsProbabilityMeasure P₀ := h₀.isProbabilityMeasure
  have hmeas : AEMeasurable (fun ω => annulusBallMassRatio (μ₀ ω) 0 0) P₀ :=
    (measurable_annulusBallMassRatio 0 0).comp_aemeasurable (h₀.aemeasurable_lqgMeasure hμ₀)
  have hpos : ∀ᵐ ω ∂P₀, 0 < annulusBallMassRatio (μ₀ ω) 0 0 := by
    filter_upwards [hfull γ α₀ hγ hγ2 hα Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀, hμ₀] with ω hf hl
    let : IsLocallyFiniteMeasure (μ₀ ω) := hl.isLocallyFiniteMeasure
    have hm := dyadicAnnulusMasses_pos_finite (μ₀ ω) hf 0 0
    exact annulusBallMassRatio_pos (μ₀ ω) 0 0 hm.1.1 hm.1.2 hm.2.1 hm.2.2
  obtain ⟨m, hm, hsmall⟩ := Section6.exists_small_threshold_of_aemeasurable P₀ hmeas hpos hδ
  refine ⟨m, hm, ?_⟩
  intro Ω _ P hC hcirc μ h hμ hAff hCC n
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hd := ((h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ).comp
    (measurable_annulusBallMassRatio 0 0)).trans
      (identDistrib_lqg_annulusBallMassRatio hγ hγ2 hα h hμ hAff hCC n)
  have hball : ∀ᵐ ω ∂P, μ ω (ball 0 (dyadicScale n)) ≠ 0 ∧
      μ ω (ball 0 (dyadicScale n)) ≠ ∞ := by
    filter_upwards [hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ, hμ] with ω hf hl
    let : IsLocallyFiniteMeasure (μ ω) := hl.isLocallyFiniteMeasure
    exact (dyadicAnnulusMasses_pos_finite (μ ω) hf 0 n).2
  calc
    P {ω | ¬ AnnulusBallComparison (μ ω) n 0 m} ≤
        P {ω | annulusBallMassRatio (μ ω) n 0 < m} := by
      apply measure_mono_ae
      filter_upwards [hball] with ω ⟨hb, hbtop⟩ hbad
      by_contra hnot
      exact hbad (annulusBallComparison_of_le_massRatio (μ ω) n 0 m hb hbtop
        (le_of_not_gt hnot))
    _ = P₀ {ω | annulusBallMassRatio (μ₀ ω) 0 0 < m} :=
      hd.symm.measure_mem_eq measurableSet_Iio
    _ ≤ δ := hsmall

end HarmonicBalls

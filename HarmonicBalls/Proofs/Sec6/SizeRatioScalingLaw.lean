import HarmonicBalls.Proofs.Sec6.BallMassSizeWindow
import HarmonicBalls.Proofs.Sec8.BallMassSizeScaling
import HarmonicBalls.Proofs.Sec8.GreenPotentialScaling
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling

/-! # Scaling laws for very-good-annulus size ratios -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

universe u

/-- The centred ball-mass size ratios have a common law at all positive
scales, under the staged affine and coordinate-change inputs. -/
theorem identDistrib_lqg_ballMassSizeRatio_scale
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    IdentDistrib (fun ω => annulusBallMassSize (μ ω) β 1 0 /
      (μ ω) (annulus 0 (1 / 4) (2 * 1)))
      (fun ω => annulusBallMassSize (μ ω) β ρ 0 /
      (μ ω) (annulus 0 (ρ / 4) (2 * ρ))) P P := by
  have hd := (hgff.identDistrib_normalizedPullback hAff hCC hγ hγ₂ hα hμ hρ).comp
    (measurable_annulusBallMassSize_ratio β 1 0 (by norm_num))
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, normalizedPullbackMeasure]
  rw [annulusBallMassSize_smul _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
    Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusBallMassRatioSize_map_inv_smul _ hρ]
  simp

/-- The centred Green-potential size ratios have a common law at all
positive scales, under the staged affine and coordinate-change inputs. -/
theorem identDistrib_lqg_greenSizeRatio_scale
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IdentDistrib (fun ω => annulusGreenPotentialSup (μ ω) 0 (1 / 4) (2 * 1) /
      (μ ω) (annulus 0 (1 / 4) (2 * 1)))
      (fun ω => annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
      (μ ω) (annulus 0 (ρ / 4) (2 * ρ))) P P := by
  have hd := (hgff.identDistrib_normalizedPullback hAff hCC hγ hγ₂ hα hμ hρ).comp
    (measurable_annulusGreenPotentialRatio_zero 1)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, normalizedPullbackMeasure]
  rw [annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusGreenPotentialRatio_map_inv_smul _ hρ]
  simp

/-- A single pair of size windows works at every positive centred scale,
conditional on volume growth and the staged scaling inputs. -/
theorem exists_veryGood_size_windows_uniform_scale
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ α₀ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hβ : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ ρ : ℝ, 0 < ρ →
      P {ω | annulusBallMassSize (μ ω) β ρ 0 / (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h₁, h₂⟩ :=
    exists_veryGood_size_windows_of_volumeGrowth hgrowth P hγ hγ₂ hα hβ hgff hμ
      (ρ := 1) (by norm_num) hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, ?_⟩
  intro ρ hρ
  have heq₁ := (identDistrib_lqg_ballMassSizeRatio_scale hγ hγ₂ hα hgff hμ hAff hCC β hρ).measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))ᶜ)
  have heq₂ := (identDistrib_lqg_greenSizeRatio_scale hγ hγ₂ hα hgff hμ hAff hCC hρ).measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))ᶜ)
  exact ⟨heq₁.symm ▸ h₁, heq₂.symm ▸ h₂⟩

end HarmonicBalls.Section6

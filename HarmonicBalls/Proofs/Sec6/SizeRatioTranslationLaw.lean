import HarmonicBalls.Proofs.Sec6.SizeRatioScalingLaw
import HarmonicBalls.Proofs.Sec6.BallMassTranslation
import HarmonicBalls.Proofs.Sec6.GreenSizeTranslation

/-! # Translation laws for very-good-annulus size ratios -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

universe u

/-- The translated measure assigns to a centred annulus the mass assigned by
the original measure to the translated annulus. -/
theorem map_sub_annulus (μ : Measure ℂ) (z : ℂ) (a b : ℝ) :
    (μ.map (fun w : ℂ => w - z)) (annulus 0 a b) = μ (annulus z a b) := by
  rw [Measure.map_apply (by fun_prop)
    (show MeasurableSet (annulus (0 : ℂ) a b) from
      (isOpen_ball.sdiff isClosed_closedBall).measurableSet)]
  congr 1
  ext w
  simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]

/-- Whole-plane ball-mass size ratios have a common law at every centre,
under the staged affine and coordinate-change inputs. -/
theorem identDistrib_lqg_ballMassSizeRatio_translate
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    IdentDistrib (fun ω => annulusBallMassSize (μ ω) β ρ 0 /
      (μ ω) (annulus 0 (ρ / 4) (2 * ρ)))
      (fun ω => annulusBallMassSize (μ ω) β ρ z /
      (μ ω) (annulus z (ρ / 4) (2 * ρ))) P P := by
  have hd := (identDistrib_affineMeasure hgff hμ hAff hCC hγ hγ₂ (by norm_num : (1 : ℂ) ≠ 0) z).comp
    (measurable_annulusBallMassSize_ratio β ρ 0 hρ)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, affineMeasure, div_one]
  rw [annulusBallMassSize_smul _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
    Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusBallMassSize_map_sub, map_sub_annulus]

/-- Whole-plane Green-potential size ratios have a common law at every centre,
under the staged affine and coordinate-change inputs. -/
theorem identDistrib_lqg_greenSizeRatio_translate
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {ρ : ℝ} (z : ℂ) :
    IdentDistrib (fun ω => annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
      (μ ω) (annulus 0 (ρ / 4) (2 * ρ)))
      (fun ω => annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
      (μ ω) (annulus z (ρ / 4) (2 * ρ))) P P := by
  have hd := (identDistrib_affineMeasure hgff hμ hAff hCC hγ hγ₂ (by norm_num : (1 : ℂ) ≠ 0) z).comp
    (measurable_annulusGreenPotentialRatio_zero ρ)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, affineMeasure, div_one]
  rw [annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusGreenPotentialSup_map_sub, map_sub_annulus]

/-- One pair of size windows works at all centres and positive scales for the
whole-plane field, conditional on volume growth and the staged affine laws. -/
theorem exists_wholePlane_veryGood_size_windows_uniform
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have heq : γ * (lqgQ γ - 0) = 2 + γ ^ 2 / 2 := by
    unfold lqgQ
    field_simp
    ring
  have hβ' : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - 0)) < β := by
    apply max_lt hβ
    rw [heq]
    nlinarith
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h⟩ :=
    exists_veryGood_size_windows_uniform_scale hgrowth P hγ hγ₂ hQ hβ' hgff hμ hAff hCC hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, ?_⟩
  intro ρ hρ z
  have heq₁ := (identDistrib_lqg_ballMassSizeRatio_translate hγ hγ₂ hgff hμ hAff hCC β hρ z).measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))ᶜ)
  have heq₂ := (identDistrib_lqg_greenSizeRatio_translate hγ hγ₂ hgff hμ hAff hCC (ρ := ρ) z).measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))ᶜ)
  exact ⟨heq₁.symm ▸ (h ρ hρ).1, heq₂.symm ▸ (h ρ hρ).2⟩

end HarmonicBalls.Section6

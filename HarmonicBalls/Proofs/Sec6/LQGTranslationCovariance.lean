import HarmonicBalls.Proofs.Sec6.WeakerSingularityExistence
import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation
import HarmonicBalls.Proofs.Sec6.AffineMeasureLaw
import HarmonicBalls.Proofs.Sec6.SizeRatioTranslationLaw

/-! # Translation covariance of LQG limits

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
Translations preserve the dyadic approximation scales, so their covariance
follows directly from the definition of the LQG limit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal

/-- Translation covariance of LQG limits along the same dyadic scales. -/
theorem isLQGLimit_translate {γ : ℝ} {h : ℝ → ℂ → ℝ} {μ : Measure ℂ}
    (hμ : IsLQGLimit γ h μ)
    (hc : ∀ n, Continuous (h (dyadicScale n))) (b : ℂ) :
    IsLQGLimit γ (fun r z => h r (z + b)) (μ.map (fun z => z - b)) := by
  constructor
  · exact isLocallyFiniteMeasure_map_sub_right hμ.isLocallyFiniteMeasure b
  · intro φ hφ hφc
    let ψ : ℂ → ℝ := fun z => φ (z - b)
    have hψ : Continuous ψ := hφ.comp (continuous_id.sub continuous_const)
    have hψc : HasCompactSupport ψ := by
      simpa [ψ, sub_eq_add_neg, Function.comp_def] using
        hφc.comp_homeomorph (Homeomorph.addRight (-b))
    have hi := hμ.tendsto_integral ψ hψ hψc
    have hmap : (∫ z, φ z ∂(μ.map (fun z => z - b))) = ∫ z, ψ z ∂μ := by
      rw [integral_map (by fun_prop) hφ.aestronglyMeasurable]
    rw [hmap]
    convert hi using 1
    funext n
    let r := dyadicScale n
    let w : ℂ → ℝ := fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ * h r z)
    have hw : Continuous w := continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (hc n)))
    have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg
      (Real.rpow_nonneg (dyadicScale_pos n).le _) (Real.exp_nonneg _)
    change (∫ z, φ z ∂(volume.withDensity fun z => ENNReal.ofReal (w (z + b)))) =
      ∫ z, ψ z ∂(volume.withDensity fun z => ENNReal.ofReal (w z))
    have hw' : Continuous (fun z : ℂ => w (z + b)) :=
      hw.comp (continuous_id.add continuous_const)
    rw [integral_withDensity_nonnegative volume (fun z => w (z + b)) φ hw'
      (fun z => hw0 (z + b)), integral_withDensity_nonnegative volume w ψ hw hw0]
    have ht := integral_add_right_eq_self (μ := volume) (fun z : ℂ => ψ z * w z) b
    simpa only [ψ, add_sub_cancel_right] using ht

/-- Translation covariance holds for all centres on one full-measure event. -/
theorem ae_isLQGLimit_translate_all
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ b : ℂ,
      IsLQGLimit γ (affineCircle hcirc 1 b ω) (affineMeasure γ hcirc μ 1 b ω) := by
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (hcirc ω (dyadicScale n)) := by
    filter_upwards [ae_all_iff.mpr (fun n => hG.ae_continuous_fieldCircleAverage 0
      (dyadicScale_pos n))] with ω hω n
    simpa only [fieldCircleAverage_zero] using hω n
  filter_upwards [hμ, hc] with ω hω hc b
  rw [fieldCircleAverage_zero] at hω
  have h := (isLQGLimit_translate hω hc b).add_const (-(hcirc ω 1 b))
  change IsLQGLimit γ (fun r z => hcirc ω (‖(1 : ℂ)‖ * r) ((1 : ℂ) * z + b) -
    hcirc ω ‖(1 : ℂ)‖ b) (affineMeasure γ hcirc μ 1 b ω)
  simpa [affineMeasure, norm_one, one_mul, Real.log_one,
    mul_zero, add_zero, div_one, sub_eq_add_neg] using h

/-- The normalized translate of an LQG measure is the LQG measure of the
normalized translated field, without an affine coordinate-change input. -/
theorem isLQGMeasureOfField_translate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (b : ℂ) : IsLQGMeasureOfField P γ 0 (affineCircle hcirc 1 b)
      (affineMeasure γ hcirc μ 1 b) := by
  filter_upwards [ae_isLQGLimit_translate_all hG hμ] with ω hω
  simpa only [fieldCircleAverage_zero] using hω b

/-- Normalized translated whole-plane LQG measures have a common law using
only the affine GFF invariance input. -/
theorem identDistrib_translateMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (b : ℂ) :
    IdentDistrib μ (affineMeasure γ hcirc μ 1 b) P P := by
  have hG' := hAff hG 1 one_ne_zero b
  exact identDistrib_lqgMeasure_of_gff hG hG' hμ (isLQGMeasureOfField_translate hG hμ b)

/-- The normalized ball-mass size ratio has the same law at every fixed
centre without a coordinate-change hypothesis. -/
theorem identDistrib_lqg_ballMassSizeRatio_translate_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    IdentDistrib (fun ω => annulusBallMassSize (μ ω) β ρ 0 /
      (μ ω) (annulus 0 (ρ / 4) (2 * ρ)))
      (fun ω => annulusBallMassSize (μ ω) β ρ z /
      (μ ω) (annulus z (ρ / 4) (2 * ρ))) P P := by
  have hd := (identDistrib_translateMeasure hG hμ hAff z).comp
    (measurable_annulusBallMassSize_ratio β ρ 0 hρ)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, affineMeasure, div_one]
  rw [annulusBallMassSize_smul _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
    Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusBallMassSize_map_sub, map_sub_annulus]

/-- The normalized Green-potential size ratio has the same law at every
fixed centre without a coordinate-change hypothesis. -/
theorem identDistrib_lqg_greenSizeRatio_translate_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) {ρ : ℝ} (z : ℂ) :
    IdentDistrib (fun ω => annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
      (μ ω) (annulus 0 (ρ / 4) (2 * ρ)))
      (fun ω => annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
      (μ ω) (annulus z (ρ / 4) (2 * ρ))) P P := by
  have hd := (identDistrib_translateMeasure hG hμ hAff z).comp
    (measurable_annulusGreenPotentialRatio_zero ρ)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, affineMeasure, div_one]
  rw [annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusGreenPotentialSup_map_sub, map_sub_annulus]

end HarmonicBalls.Section6

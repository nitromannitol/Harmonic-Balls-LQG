import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance
import HarmonicBalls.Proofs.Sec6.UniversalSizeWindows

/-! # Fixed-scale universal size windows

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. At a fixed radius, translation
covariance yields size windows uniform in the centre and the realization.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

universe u

/-- At a fixed positive radius, one pair of size windows works at every centre
and in every whole-plane realization, under volume growth and the affine
field invariance. The windows may depend on the radius. -/
theorem exists_universal_wholePlane_size_windows_fixed_scale
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ z : ℂ,
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  let : IsProbabilityMeasure P₀ := h₀.isProbabilityMeasure
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have heq : γ * (lqgQ γ - 0) = 2 + γ ^ 2 / 2 := by
    unfold lqgQ
    field_simp
    ring
  have hβ' : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - 0)) < β := by
    apply max_lt hβ
    rw [heq]
    nlinarith
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hM, hG⟩ :=
    exists_veryGood_size_windows_of_volumeGrowth hgrowth P₀ hγ hγ₂ hQ hβ' h₀ hμ₀ hρ hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, ?_⟩
  intro Ω _ P hC hcirc μ h hμ hAff z
  have hlaw := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have hd₁ := (hlaw.comp (measurable_annulusBallMassSize_ratio β ρ 0 hρ)).trans
    (identDistrib_lqg_ballMassSizeRatio_translate_of_affine h hμ hAff β hρ z)
  have hd₂ := (hlaw.comp (measurable_annulusGreenPotentialRatio_zero ρ)).trans
    (identDistrib_lqg_greenSizeRatio_translate_of_affine h hμ hAff (ρ := ρ) z)
  have heq₁ := hd₁.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))ᶜ)
  have heq₂ := hd₂.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))ᶜ)
  exact ⟨heq₁ ▸ hM, heq₂ ▸ hG⟩


/-- Fixed-radius size windows also hold for singular fields on annuli separated
from the origin, under the existence and affine field inputs. -/
theorem exists_universal_lqg_size_windows_fixed_scale
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc →
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ z : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus z (ρ / 4) (2 * ρ)) →
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h⟩ :=
    exists_universal_wholePlane_size_windows_fixed_scale hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀ hρ hδ
  let e : ℝ := -(γ * α₀)
  let K : ℝ := ((401 : ℝ) ^ |e|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C₁m / K, K * C₁p, C₂m / K, K * C₂p,
    div_pos h₁m hK, mul_pos hK h₁p, div_pos h₂m hK, mul_pos hK h₂p, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ hEx hAff z hd
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  have ht := size_window_failure_le_of_singular_weight P
    (β := β) (C₁m := C₁m) (C₁p := C₁p) (C₂m := C₂m) (C₂p := C₂p) hρ hd hweight
  have hw := h Ω P hC hcirc ν hgff hν hAff z
  exact ⟨ht.1.trans hw.1, ht.2.trans hw.2⟩

end HarmonicBalls.Section6

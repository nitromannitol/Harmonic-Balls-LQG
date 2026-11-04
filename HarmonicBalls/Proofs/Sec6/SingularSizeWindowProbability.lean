import HarmonicBalls.Proofs.Sec6.SizeRatioSingularWeight
import HarmonicBalls.Proofs.Sec6.SizeRatioTranslationLaw
import HarmonicBalls.Proofs.Sec2.SingularWeight

/-! # Probability bounds for size windows with a logarithmic singularity -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Singular weighting transfers each size-window failure bound separately. -/
theorem size_window_failure_le_of_singular_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ ν : Ω → Measure ℂ}
    {ρ e β : ℝ} {x₀ : ℂ} {C₁m C₁p C₂m C₂p : ℝ}
    (hρ : 0 < ρ) (hd : ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)))
    (hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    let K : ℝ := ((401 : ℝ) ^ |e|) ^ 2
    P {ω | annulusBallMassSize (μ ω) β ρ x₀ / (μ ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∉
      Icc (ENNReal.ofReal (C₁m / K)) (ENNReal.ofReal (K * C₁p))} ≤
      P {ω | annulusBallMassSize (ν ω) β ρ x₀ / (ν ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∉
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ∧
    P {ω | annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) (2 * ρ) /
      (μ ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∉
      Icc (ENNReal.ofReal (C₂m / K)) (ENNReal.ofReal (K * C₂p))} ≤
      P {ω | annulusGreenPotentialSup (ν ω) x₀ (ρ / 4) (2 * ρ) /
      (ν ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∉
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} := by
  let K : ℝ := ((401 : ℝ) ^ |e|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hdiv : ∀ a : ℝ, ENNReal.ofReal (a / K) = ENNReal.ofReal a / ENNReal.ofReal K :=
    fun a => ENNReal.ofReal_div_of_pos hK
  have hmul : ∀ a : ℝ, ENNReal.ofReal (K * a) = ENNReal.ofReal K * ENNReal.ofReal a :=
    fun a => ENNReal.ofReal_mul hK.le
  constructor <;> apply measure_mono_ae <;> filter_upwards [hweight] with ω hω
  · intro hbad hgood
    obtain ⟨c, hc⟩ := isComparableOnWith_size_annulus_of_weight hρ hd hω
    have hs := annulusBallMassSize_comparableWith_on_annulus hc hρ β
    apply hbad
    rw [hdiv, hmul]
    exact ratio_mem_of_comparableWith hc.scale_ne_zero hc.scale_ne_top hc.distortion_ne_zero
      hc.distortion_ne_top hs.1 hs.2 (hc.le_apply Subset.rfl) (hc.apply_le Subset.rfl) hgood
  · intro hbad hgood
    obtain ⟨c, hc⟩ := isComparableOnWith_size_annulus_of_weight hρ hd hω
    have hs := annulusGreenPotentialSup_comparableWith hc
    apply hbad
    rw [hdiv, hmul]
    exact ratio_mem_of_comparableWith hc.scale_ne_zero hc.scale_ne_top hc.distortion_ne_zero
      hc.distortion_ne_top hs.1 hs.2 (hc.le_apply Subset.rfl) (hc.apply_le Subset.rfl) hgood


/-- Volume growth and the staged affine laws give uniform size-window bounds for
an LQG measure with a singularity, given its Weyl identity with the whole-plane measure. -/
theorem exists_singular_veryGood_size_windows_uniform
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ β e : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus z (ρ / 4) (2 * ρ)) →
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h⟩ :=
    exists_wholePlane_veryGood_size_windows_uniform hgrowth P hγ hγ₂ hβ hgff hν hAff hCC hδ
  let K : ℝ := ((401 : ℝ) ^ |e|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C₁m / K, K * C₁p, C₂m / K, K * C₂p,
    div_pos h₁m hK, mul_pos hK h₁p, div_pos h₂m hK, mul_pos hK h₂p, ?_⟩
  intro ρ hρ z hd
  have htransfer := size_window_failure_le_of_singular_weight P
    (β := β) (C₁m := C₁m) (C₁p := C₁p) (C₂m := C₂m) (C₂p := C₂p) hρ hd hweight
  exact ⟨htransfer.1.trans (h ρ hρ z).1, htransfer.2.trans (h ρ hρ z).2⟩


/-- Uniform singular-field size windows from volume growth and the staged LQG inputs. -/
theorem exists_lqg_veryGood_size_windows_uniform
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ α₀ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (_hα : α₀ < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hEx : LQGMeasureExistence P γ 0 hC hcirc)
    (hW : LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus z (ρ / 4) (2 * ρ)) →
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α₀)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  exact exists_singular_veryGood_size_windows_uniform hgrowth P hγ hγ₂ hβ
    hgff hν hAff hCC hweight hδ

end HarmonicBalls.Section6

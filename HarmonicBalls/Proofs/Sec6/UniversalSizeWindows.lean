import HarmonicBalls.Proofs.Sec6.SingularSizeWindowProbability
import HarmonicBalls.Proofs.Sec8.LQGUniversalMeasureLaw

/-! # Model-independent size-window bounds

One reference realization fixes the size-window constants. The law of the
LQG measure transfers them to all other realizations. The LQG existence,
Weyl, affine and coordinate-change inputs remain explicit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

universe u

/-- One whole-plane reference realization fixes size windows for every
whole-plane realization, positive scale and center. -/
theorem exists_universal_wholePlane_size_windows
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
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
    exists_veryGood_size_windows_of_volumeGrowth hgrowth P₀ hγ hγ₂ hQ hβ' h₀ hμ₀
      (ρ := 1) (by norm_num) hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, ?_⟩
  intro Ω _ P hC hcirc μ h hμ hAff hCC ρ hρ z
  have hlaw := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have hd₁ := ((hlaw.comp (measurable_annulusBallMassSize_ratio β 1 0 (by norm_num))).trans
      (identDistrib_lqg_ballMassSizeRatio_scale hγ hγ₂ hQ h hμ hAff hCC β hρ)).trans
      (identDistrib_lqg_ballMassSizeRatio_translate hγ hγ₂ h hμ hAff hCC β hρ z)
  have hd₂ := ((hlaw.comp (measurable_annulusGreenPotentialRatio_zero 1)).trans
      (identDistrib_lqg_greenSizeRatio_scale hγ hγ₂ hQ h hμ hAff hCC hρ)).trans
      (identDistrib_lqg_greenSizeRatio_translate hγ hγ₂ h hμ hAff hCC (ρ := ρ) z)
  have heq₁ := hd₁.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))ᶜ)
  have heq₂ := hd₂.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))ᶜ)
  exact ⟨heq₁ ▸ hM, heq₂ ▸ hG⟩


/-- One whole-plane reference realization fixes the singular-field size windows
for every realization and every admissible annulus. -/
theorem exists_universal_lqg_size_windows
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (_hα : α₀ < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc → LQGMeasureWeylScaling P γ 0 hC hcirc →
        WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus z (ρ / 4) (2 * ρ)) →
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h⟩ :=
    exists_universal_wholePlane_size_windows hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀ hδ
  let e : ℝ := -(γ * α₀)
  let K : ℝ := ((401 : ℝ) ^ |e|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C₁m / K, K * C₁p, C₂m / K, K * C₂p,
    div_pos h₁m hK, mul_pos hK h₁p, div_pos h₂m hK, mul_pos hK h₂p, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ hEx hW hAff hCC ρ hρ z hd
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  have ht := size_window_failure_le_of_singular_weight P
    (β := β) (C₁m := C₁m) (C₁p := C₁p) (C₂m := C₂m) (C₂p := C₂p) hρ hd hweight
  have hw := h Ω P hC hcirc ν hgff hν hAff hCC ρ hρ z
  exact ⟨ht.1.trans hw.1, ht.2.trans hw.2⟩


/-- Model-independent size windows. If there is no whole-plane reference
realization, the hypotheses for every target realization are inconsistent. -/
theorem exists_universal_lqg_size_windows_of_inputs
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc → LQGMeasureWeylScaling P γ 0 hC hcirc →
        WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus z (ρ / 4) (2 * ρ)) →
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  classical
  by_cases href : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀),
      letI := m₀
      ∃ (P₀ : Measure Ω₀) (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ)
        (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ),
        IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, h₀, hμ₀⟩ := href
    let : MeasurableSpace Ω₀ := m₀
    exact exists_universal_lqg_size_windows hgrowth hγ hγ₂ hα hβ P₀ h₀ hμ₀ hδ
  · refine ⟨1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro Ω mΩ P hC hcirc μ hgff _ hEx _ _ _ ρ hρ z hd
    exfalso
    apply href
    have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
    obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
    exact ⟨Ω, mΩ, P, hC, hcirc, ν, hgff, hν⟩

end HarmonicBalls.Section6

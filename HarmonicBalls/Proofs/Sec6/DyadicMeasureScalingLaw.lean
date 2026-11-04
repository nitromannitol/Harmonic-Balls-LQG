import HarmonicBalls.Proofs.Sec9.LQGSpatialDilation
import HarmonicBalls.Proofs.Sec6.FixedScaleUniversalSizeWindows

/-! # Dyadic laws of normalized LQG measures

The dyadic coordinate change follows from the circle-average limit itself.
The affine invariance of the whole-plane GFF remains an explicit assumption.
The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

/-- The normalized pullback of a whole-plane LQG measure by a positive integer
power of two has the same law as the original measure. -/
theorem identDistrib_normalizedPullback_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (m : ℕ) :
    IdentDistrib μ (fun ω => normalizedPullbackMeasure γ 0 ((2 : ℝ) ^ m)
      (hcirc ω) (μ ω)) P P := by
  let k : ℝ := (2 : ℝ) ^ m
  have hk : 0 < k := by dsimp [k]; positivity
  have hG' := hAff hG (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hμ' := isLQGMeasureOfField_normalizedPullback_dyadic hG hγ.ne' hμ m
  have hμ'' : IsLQGMeasureOfField P γ 0 (affineCircle hcirc (k : ℂ) 0)
      (fun ω => normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) := by
    have hc : affineCircle hcirc (k : ℂ) 0 =
        (fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0) := by
      funext ω r z
      simp [affineCircle, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk,
        Complex.real_smul]
    rw [hc]
    exact hμ'
  exact identDistrib_lqgMeasure_of_gff hG hG' hμ hμ''


/-- Ball-mass ratios at radii differing by a power of two have the same law. -/
theorem identDistrib_lqg_ballMassSizeRatio_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (m : ℕ) (β : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IdentDistrib (fun ω => annulusBallMassSize (μ ω) β ρ 0 /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)))
      (fun ω => annulusBallMassSize (μ ω) β ((2 : ℝ) ^ m * ρ) 0 /
        (μ ω) (annulus 0 (((2 : ℝ) ^ m * ρ) / 4) (2 * ((2 : ℝ) ^ m * ρ)))) P P := by
  have hk : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hd := (identDistrib_normalizedPullback_dyadic hγ hG hμ hAff m).comp
    (measurable_annulusBallMassSize_ratio β ρ 0 hρ)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, normalizedPullbackMeasure]
  rw [annulusBallMassSize_smul _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
    Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusBallMassRatioSize_map_inv_smul _ hk]

/-- Green-potential size ratios at radii differing by a power of two have the
same law. -/
theorem identDistrib_lqg_greenSizeRatio_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (m : ℕ) (ρ : ℝ) :
    IdentDistrib (fun ω => annulusGreenPotentialSup (μ ω) 0 (ρ / 4) (2 * ρ) /
        (μ ω) (annulus 0 (ρ / 4) (2 * ρ)))
      (fun ω => annulusGreenPotentialSup (μ ω) 0 (((2 : ℝ) ^ m * ρ) / 4)
        (2 * ((2 : ℝ) ^ m * ρ)) /
        (μ ω) (annulus 0 (((2 : ℝ) ^ m * ρ) / 4) (2 * ((2 : ℝ) ^ m * ρ)))) P P := by
  have hk : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hd := (identDistrib_normalizedPullback_dyadic hγ hG hμ hAff m).comp
    (measurable_annulusGreenPotentialRatio_zero ρ)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, normalizedPullbackMeasure]
  rw [annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ (by positivity) ENNReal.ofReal_ne_top,
    annulusGreenPotentialRatio_map_inv_smul _ hk]


universe u

/-- The whole-plane size-window constants can be chosen uniformly over all
inverse dyadic radii, all centres, and all realizations. -/
theorem exists_universal_wholePlane_size_windows_dyadic
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
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ (n : ℕ) (z : ℂ),
      P {ω | annulusBallMassSize (μ ω) β (dyadicScale n) z /
        (μ ω) (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (dyadicScale n / 4) (2 * dyadicScale n) /
        (μ ω) (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h⟩ :=
    exists_universal_wholePlane_size_windows_fixed_scale hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀
      (ρ := 1) (by norm_num) hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ hAff n z
  have hw := h Ω P hC hcirc μ hgff hμ hAff 0
  have hs : (2 : ℝ) ^ n * dyadicScale n = 1 := by
    simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
  have hd₁ := (identDistrib_lqg_ballMassSizeRatio_dyadic hγ hgff hμ hAff n β
    (dyadicScale_pos n)).symm.trans
    (identDistrib_lqg_ballMassSizeRatio_translate_of_affine hgff hμ hAff β (dyadicScale_pos n) z)
  have hd₂ := (identDistrib_lqg_greenSizeRatio_dyadic hγ hgff hμ hAff n (dyadicScale n)).symm.trans
    (identDistrib_lqg_greenSizeRatio_translate_of_affine hgff hμ hAff (ρ := dyadicScale n) z)
  rw [hs] at hd₁ hd₂
  have heq₁ := hd₁.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))ᶜ)
  have heq₂ := hd₂.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))ᶜ)
  exact ⟨heq₁ ▸ hw.1, heq₂ ▸ hw.2⟩

end HarmonicBalls.Section6

import HarmonicBalls.Proofs.Sec8.LQGAnnulusComparison
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Scale invariance of annulus-to-ball mass ratios -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- A dilation pulls a ball centred at zero back to the corresponding larger ball. -/
theorem preimage_inv_smul_ball_zero {k : ℝ} (hk : 0 < k) (r : ℝ) :
    (fun x : ℂ => k⁻¹ • x) ⁻¹' ball 0 r = ball 0 (k * r) := by
  ext x
  simp only [mem_preimage, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hk]
  rw [inv_mul_lt_iff₀ hk]

/-- A dilation pulls a closed ball centred at zero back to the corresponding larger ball. -/
theorem preimage_inv_smul_closedBall_zero {k : ℝ} (hk : 0 < k) (r : ℝ) :
    (fun x : ℂ => k⁻¹ • x) ⁻¹' closedBall 0 r = closedBall 0 (k * r) := by
  ext x
  simp only [mem_preimage, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hk]
  rw [inv_mul_le_iff₀ hk]

/-- Multiplication of a measure by a finite nonzero constant leaves its mass ratio unchanged. -/
theorem annulusBallMassRatio_smul (μ : Measure ℂ) (n : ℕ) (z : ℂ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    annulusBallMassRatio (c • μ) n z = annulusBallMassRatio μ n z := by
  simp only [annulusBallMassRatio, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ hc hct]

/-- Pulling back by a dyadic dilation transports the ratio at that scale to scale zero. -/
theorem annulusBallMassRatio_map_dyadic (μ : Measure ℂ) (n : ℕ) :
    annulusBallMassRatio (μ.map (fun x : ℂ => (dyadicScale n)⁻¹ • x)) 0 0 =
      annulusBallMassRatio μ n 0 := by
  have hk := dyadicScale_pos n
  have hcont : Measurable (fun x : ℂ => (dyadicScale n)⁻¹ • x) :=
    ((continuous_const : Continuous (fun _ : ℂ => (dyadicScale n)⁻¹)).smul
      (continuous_id : Continuous (fun x : ℂ => x))).measurable
  have ha : MeasurableSet (annulus 0 (dyadicScale (0 + 1)) (dyadicScale 0)) :=
    (isOpen_nonempty_dyadicAnnulus 0 0).1.measurableSet
  have hpre : (fun x : ℂ => (dyadicScale n)⁻¹ • x) ⁻¹'
      annulus 0 (dyadicScale (0 + 1)) (dyadicScale 0) =
      annulus 0 (dyadicScale (n + 1)) (dyadicScale n) := by
    simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk]
    simp [dyadicScale, pow_succ, mul_comm]
  have hb : (fun x : ℂ => (dyadicScale n)⁻¹ • x) ⁻¹' ball 0 (dyadicScale 0) =
      ball 0 (dyadicScale n) := by
    rw [preimage_inv_smul_ball_zero hk]
    simp [dyadicScale]
  simp only [annulusBallMassRatio, Measure.map_apply hcont ha,
    Measure.map_apply hcont isOpen_ball.measurableSet, hpre, hb]

/-- The dyadic annulus-to-ball mass ratio is a measurable function of the measure. -/
theorem measurable_annulusBallMassRatio (n : ℕ) (z : ℂ) :
    Measurable (fun μ : Measure ℂ => annulusBallMassRatio μ n z) := by
  exact ENNReal.measurable_toReal.comp ((Measure.measurable_coe
    (isOpen_nonempty_dyadicAnnulus z n).1.measurableSet).div
      (Measure.measurable_coe isOpen_ball.measurableSet))

universe u

/-- Whole-plane LQG annulus-to-ball ratios at zero have a common law at all dyadic scales. -/
theorem identDistrib_lqg_annulusBallMassRatio
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc) (n : ℕ) :
    IdentDistrib (fun ω => annulusBallMassRatio (μ ω) 0 0)
      (fun ω => annulusBallMassRatio (μ ω) n 0) P P := by
  have hd := (hGFF.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ
    (dyadicScale_pos n)).comp (measurable_annulusBallMassRatio 0 0)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [Function.comp_apply, normalizedPullbackMeasure]
  rw [annulusBallMassRatio_smul]
  · exact annulusBallMassRatio_map_dyadic (μ ω) n
  · apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    positivity
  · exact ENNReal.ofReal_ne_top

/-- The annulus comparison holds at every dyadic scale with uniformly high
probability at the origin, under the staged scale-invariance inputs. -/
theorem exists_lqg_annulusBallComparison_threshold_at_zero
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m ∈ Ioo (0 : ℝ) 1, ∀ n,
      P {ω | ¬ AnnulusBallComparison (μ ω) n 0 m} ≤ δ := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hmeas : AEMeasurable (fun ω => annulusBallMassRatio (μ ω) 0 0) P :=
    (measurable_annulusBallMassRatio 0 0).comp_aemeasurable
      (hGFF.aemeasurable_lqgMeasure hμ)
  have hmass : ∀ᵐ ω ∂P, ∀ n,
      (μ ω (annulus 0 (dyadicScale (n + 1)) (dyadicScale n)) ≠ 0 ∧
        μ ω (annulus 0 (dyadicScale (n + 1)) (dyadicScale n)) ≠ ∞) ∧
      (μ ω (ball 0 (dyadicScale n)) ≠ 0 ∧ μ ω (ball 0 (dyadicScale n)) ≠ ∞) := by
    filter_upwards [hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hf hl n
    let : IsLocallyFiniteMeasure (μ ω) := hl.isLocallyFiniteMeasure
    exact dyadicAnnulusMasses_pos_finite (μ ω) hf 0 n
  have hpos : ∀ᵐ ω ∂P, 0 < annulusBallMassRatio (μ ω) 0 0 := by
    filter_upwards [hmass] with ω hω
    exact annulusBallMassRatio_pos (μ ω) 0 0 (hω 0).1.1 (hω 0).1.2 (hω 0).2.1 (hω 0).2.2
  have hball : ∀ n, ∀ᵐ ω ∂P, μ ω (ball 0 (dyadicScale n)) ≠ 0 ∧
      μ ω (ball 0 (dyadicScale n)) ≠ ∞ := by
    intro n
    filter_upwards [hmass] with ω hω
    exact (hω n).2
  have hlaw : ∀ n a, P {ω | annulusBallMassRatio (μ ω) n 0 < a} =
      P {ω | annulusBallMassRatio (μ ω) 0 0 < a} := by
    intro n a
    exact (identDistrib_lqg_annulusBallMassRatio hγ hγ2 hα hGFF hμ hAff hCC n).symm.measure_mem_eq
      measurableSet_Iio
  exact exists_annulusBallComparison_threshold_of_equal_lower_tails P μ 0 hmeas hpos hball hlaw hδ

end HarmonicBalls

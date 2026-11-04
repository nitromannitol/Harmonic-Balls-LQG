import HarmonicBalls.Proofs.Sec8.AnnulusRatioScaling

/-! # Stationarity of annulus-comparison indicators -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- Pulling back by a dyadic dilation shifts the annulus comparison by the
corresponding number of scales. -/
theorem annulusBallComparison_map_dyadic (μ : Measure ℂ) (j n : ℕ) (m : ℝ) :
    AnnulusBallComparison (μ.map (fun x : ℂ => (dyadicScale j)⁻¹ • x)) n 0 m ↔
      AnnulusBallComparison μ (j + n) 0 m := by
  have hk := dyadicScale_pos j
  have hcont : Measurable (fun x : ℂ => (dyadicScale j)⁻¹ • x) :=
    ((continuous_const : Continuous (fun _ : ℂ => (dyadicScale j)⁻¹)).smul
      (continuous_id : Continuous (fun x : ℂ => x))).measurable
  have ha : MeasurableSet (annulus 0 (dyadicScale (n + 1)) (dyadicScale n)) :=
    (isOpen_nonempty_dyadicAnnulus 0 n).1.measurableSet
  have hpre : (fun x : ℂ => (dyadicScale j)⁻¹ • x) ⁻¹'
      annulus 0 (dyadicScale (n + 1)) (dyadicScale n) =
      annulus 0 (dyadicScale (j + n + 1)) (dyadicScale (j + n)) := by
    rw [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk, annulus]
    simp [dyadicScale, pow_add, mul_assoc]
  have hb : (fun x : ℂ => (dyadicScale j)⁻¹ • x) ⁻¹' ball 0 (dyadicScale n) =
      ball 0 (dyadicScale (j + n)) := by
    rw [preimage_inv_smul_ball_zero hk]
    simp [dyadicScale, pow_add]
  simp only [AnnulusBallComparison, Measure.map_apply hcont ha,
    Measure.map_apply hcont isOpen_ball.measurableSet, hpre, hb]

/-- Multiplying a measure by a finite nonzero constant preserves annulus comparison. -/
theorem annulusBallComparison_smul (μ : Measure ℂ) (n : ℕ) (z : ℂ) (m : ℝ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    AnnulusBallComparison (c • μ) n z m ↔ AnnulusBallComparison μ n z m := by
  simp only [AnnulusBallComparison, Measure.smul_apply, smul_eq_mul]
  rw [mul_left_comm (ENNReal.ofReal m) c, ENNReal.mul_le_mul_iff_right hc hct]

/-- Annulus comparison is a measurable property of a measure. -/
theorem measurableSet_annulusBallComparison (n : ℕ) (z : ℂ) (m : ℝ) :
    MeasurableSet {μ : Measure ℂ | AnnulusBallComparison μ n z m} := by
  exact measurableSet_le (measurable_const.mul (Measure.measurable_coe isOpen_ball.measurableSet))
    (Measure.measurable_coe (isOpen_nonempty_dyadicAnnulus z n).1.measurableSet)

universe u

open Classical in
/-- Under scale invariance of the LQG measure, the entire sequence of
annulus-comparison indicators at the origin is stationary. -/
theorem identDistrib_lqg_annulusBallComparison_sequence
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc) (m : ℝ) (j : ℕ) :
    IdentDistrib
      (fun ω n => if AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if AnnulusBallComparison (μ ω) (j + n) 0 m then (1 : ℝ) else 0) P P := by
  classical
  let F : Measure ℂ → ℕ → ℝ := fun ν n =>
    if AnnulusBallComparison ν n 0 m then 1 else 0
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro n
    exact measurable_const.piecewise (measurableSet_annulusBallComparison n 0 m) measurable_const
  have hd := (hGFF.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ
    (dyadicScale_pos j)).comp hF
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  funext n
  simp only [Function.comp_apply, F, normalizedPullbackMeasure]
  rw [annulusBallComparison_smul, annulusBallComparison_map_dyadic]
  · apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    positivity
  · exact ENNReal.ofReal_ne_top

open Classical in
/-- Measurability and scale transport of the very-good-annulus event yield
stationarity of the joint very-good and comparison indicators. -/
theorem identDistrib_lqg_veryGoodComparable_sequence_of_transport
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (βminus : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hmeas : ∀ n, MeasurableSet {ν : Measure ℂ |
      IsVeryGoodAnnulus ν βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃})
    (htransport : ∀ᵐ ω ∂P, ∀ n,
      IsVeryGoodAnnulus (normalizedPullbackMeasure γ α₀ (dyadicScale 1) (hcirc ω) (μ ω))
        βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus (μ ω) βminus (dyadicScale (1 + n)) 0 N₀ a b C₁m C₁p C₂m C₂p C₃) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  let F : Measure ℂ → ℕ → ℝ := fun ν n =>
    if IsVeryGoodAnnulus ν βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison ν n 0 m then 1 else 0
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro n
    exact measurable_const.piecewise ((hmeas n).inter
      (measurableSet_annulusBallComparison n 0 m)) measurable_const
  have hd := (hGFF.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ
    (dyadicScale_pos 1)).comp hF
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [htransport] with ω hω
  funext n
  simp only [Function.comp_apply, F]
  have hc : AnnulusBallComparison
      (normalizedPullbackMeasure γ α₀ (dyadicScale 1) (hcirc ω) (μ ω)) n 0 m ↔
      AnnulusBallComparison (μ ω) (1 + n) 0 m := by
    simp only [normalizedPullbackMeasure]
    rw [annulusBallComparison_smul, annulusBallComparison_map_dyadic]
    · apply ne_of_gt
      apply ENNReal.ofReal_pos.mpr
      positivity
    · exact ENNReal.ofReal_ne_top
  rw [hω n, hc]

end HarmonicBalls

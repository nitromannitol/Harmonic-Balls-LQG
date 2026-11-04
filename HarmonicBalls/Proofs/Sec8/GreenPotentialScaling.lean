import HarmonicBalls.Proofs.Sec5.GreenScaling
import HarmonicBalls.Proofs.Sec8.AnnulusRatioScaling

/-! # Dilation of annular Green potentials -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- Dilation transports the annular Green potential at a fixed pole. -/
theorem annulusGreenPotential_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (a b : ℝ) (x : ℂ) :
    (∫⁻ y in annulus (0 : ℂ) a b,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) x y))
        ∂(μ.map (fun z : ℂ => k⁻¹ • z))) =
    ∫⁻ y in annulus (0 : ℂ) (k * a) (k * b),
      (if y = k • x then ∞ else ENNReal.ofReal (greenFunction (ball 0 (k * b)) (k • x) y)) ∂μ := by
  have hg : Measurable (fun z : ℂ => k⁻¹ • z) := by fun_prop
  have hf : Measurable (fun y : ℂ => if y = x then (∞ : ℝ≥0∞)
      else ENNReal.ofReal (greenFunction (ball 0 b) x y)) :=
    Measurable.ite (measurableSet_singleton x) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  have hs : MeasurableSet (annulus (0 : ℂ) a b) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  rw [setLIntegral_map hs hf hg]
  have hp : (fun z : ℂ => k⁻¹ • z) ⁻¹' annulus (0 : ℂ) a b =
      annulus 0 (k * a) (k * b) := by
    simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk]
  rw [hp]
  apply lintegral_congr
  intro y
  have hy : k • (k⁻¹ • y) = y := by simp [hk.ne']
  have heq : k⁻¹ • y = x ↔ y = k • x := by
    constructor
    · intro h
      calc
        y = k • (k⁻¹ • y) := hy.symm
        _ = k • x := congrArg (fun z : ℂ => k • z) h
    · intro h
      rw [h, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  by_cases h : y = k • x
  · subst y
    simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, ite_true]
  · simp only [h, heq.not.mpr h, ite_false]
    exact congrArg ENNReal.ofReal (by
      simpa only [hy] using (greenFunction_ball_smul hk x (k⁻¹ • y)).symm)

/-- The supremum of the annular Green potential is invariant under simultaneous
spatial dilation of the measure and annulus. -/
theorem annulusGreenPotentialSup_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (a b : ℝ) :
    annulusGreenPotentialSup (μ.map (fun z : ℂ => k⁻¹ • z)) 0 a b =
      annulusGreenPotentialSup μ 0 (k * a) (k * b) := by
  have hp : (fun z : ℂ => k⁻¹ • z) ⁻¹' annulus (0 : ℂ) a b =
      annulus 0 (k * a) (k * b) := by
    simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk]
  have hmem (x : ℂ) : x ∈ annulus (0 : ℂ) a b ↔
      k • x ∈ annulus (0 : ℂ) (k * a) (k * b) := by
    rw [← hp]
    simp only [mem_preimage, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  unfold annulusGreenPotentialSup
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    rw [annulusGreenPotential_map_inv_smul μ hk a b x]
    exact le_iSup_of_le (k • x) (le_iSup_of_le ((hmem x).mp hx) le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    have hx' : k⁻¹ • x ∈ annulus (0 : ℂ) a b := by
      have := hx
      rw [← hp] at this
      exact this
    have hi : (∫⁻ y in annulus (0 : ℂ) a b,
        (if y = k⁻¹ • x then ∞ else
          ENNReal.ofReal (greenFunction (ball 0 b) (k⁻¹ • x) y))
          ∂(μ.map (fun z : ℂ => k⁻¹ • z))) ≤
      ⨆ z ∈ annulus (0 : ℂ) a b, ∫⁻ y in annulus (0 : ℂ) a b,
        (if y = z then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) z y))
          ∂(μ.map (fun z : ℂ => k⁻¹ • z)) :=
      le_iSup_of_le (k⁻¹ • x) (le_iSup_of_le hx' le_rfl)
    rw [annulusGreenPotential_map_inv_smul μ hk a b (k⁻¹ • x)] at hi
    simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hi

/-- The normalized Green-potential size in the very-good-annulus event is
preserved by positive spatial dilation. -/
theorem annulusGreenPotentialRatio_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (ρ : ℝ) :
    annulusGreenPotentialSup (μ.map (fun z : ℂ => k⁻¹ • z)) 0 (ρ / 4) (2 * ρ) /
        (μ.map (fun z : ℂ => k⁻¹ • z)) (annulus 0 (ρ / 4) (2 * ρ)) =
      annulusGreenPotentialSup μ 0 ((k * ρ) / 4) (2 * (k * ρ)) /
        μ (annulus 0 ((k * ρ) / 4) (2 * (k * ρ))) := by
  have hg : Measurable (fun z : ℂ => k⁻¹ • z) := by fun_prop
  have hs : MeasurableSet (annulus (0 : ℂ) (ρ / 4) (2 * ρ)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  rw [annulusGreenPotentialSup_map_inv_smul μ hk, Measure.map_apply hg hs]
  simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
    preimage_inv_smul_closedBall_zero hk]
  congr 2 <;> ring

end HarmonicBalls

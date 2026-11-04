import HarmonicBalls.Proofs.Sec8.AnnulusRatioScaling

/-! # Dilation of annular ball-mass sizes -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- A positive dilation pulls back a ball with arbitrary center. -/
theorem preimage_inv_smul_ball {k : ℝ} (hk : 0 < k) (z : ℂ) (r : ℝ) :
    (fun x : ℂ => k⁻¹ • x) ⁻¹' ball z r = ball (k • z) (k * r) := by
  ext x
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  have heq : k⁻¹ • x - z = k⁻¹ • (x - k • z) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hk,
    inv_mul_lt_iff₀ hk]

/-- Pullback of an arbitrary centered ball by a positive dilation. -/
theorem map_inv_smul_ball (μ : Measure ℂ) {k : ℝ} (hk : 0 < k) (z : ℂ) (r : ℝ) :
    (μ.map (fun x : ℂ => k⁻¹ • x)) (ball z r) = μ (ball (k • z) (k * r)) := by
  rw [Measure.map_apply (by fun_prop) isOpen_ball.measurableSet,
    preimage_inv_smul_ball hk]

/-- The annular ball-mass size is preserved by positive spatial dilation. -/
theorem annulusBallMassSize_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (β ρ : ℝ) :
    annulusBallMassSize (μ.map (fun x : ℂ => k⁻¹ • x)) β ρ 0 =
      annulusBallMassSize μ β (k * ρ) 0 := by
  have hp : (fun z : ℂ => k⁻¹ • z) ⁻¹' annulus (0 : ℂ) (ρ / 2) ρ =
      annulus 0 ((k * ρ) / 2) (k * ρ) := by
    simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk]
    congr 2; ring
  have hmem (z : ℂ) : z ∈ annulus (0 : ℂ) (ρ / 2) ρ ↔
      k • z ∈ annulus (0 : ℂ) ((k * ρ) / 2) (k * ρ) := by
    rw [← hp]
    simp only [mem_preimage, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  unfold annulusBallMassSize
  apply le_antisymm
  · refine le_iInf fun z => le_iInf fun hz => le_iInf fun r => le_iInf fun hr => ?_
    have hz' : k⁻¹ • z ∈ annulus (0 : ℂ) (ρ / 2) ρ := by
      rw [← hp] at hz
      exact hz
    have hr' : k⁻¹ * r ∈ Ioo (0 : ℝ) (ρ / 4) := by
      constructor
      · exact mul_pos (inv_pos.mpr hk) hr.1
      · have ht := mul_lt_mul_of_pos_left hr.2 (inv_pos.mpr hk)
        have he : k⁻¹ * ((k * ρ) / 4) = ρ / 4 := by field_simp
        simpa only [he] using ht
    calc
      _ ≤ (μ.map (fun x : ℂ => k⁻¹ • x)) (ball (k⁻¹ • z) (k⁻¹ * r)) /
          ENNReal.ofReal (((k⁻¹ * r) / ρ) ^ β) :=
        iInf_le_of_le (k⁻¹ • z) (iInf_le_of_le hz'
          (iInf_le_of_le (k⁻¹ * r) (iInf_le_of_le hr' le_rfl)))
      _ = _ := by
        rw [map_inv_smul_ball μ hk]
        have hrat : (k⁻¹ * r) / ρ = r / (k * ρ) := by field_simp
        have hrad : k * (k⁻¹ * r) = r := by field_simp
        simp only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul, hrad, hrat]
  · refine le_iInf fun z => le_iInf fun hz => le_iInf fun r => le_iInf fun hr => ?_
    have hr' : k * r ∈ Ioo (0 : ℝ) ((k * ρ) / 4) := by
      constructor
      · exact mul_pos hk hr.1
      · have ht := mul_lt_mul_of_pos_left hr.2 hk
        have he : k * (ρ / 4) = (k * ρ) / 4 := by ring
        simpa only [he] using ht
    calc
      _ ≤ μ (ball (k • z) (k * r)) / ENNReal.ofReal (((k * r) / (k * ρ)) ^ β) :=
        iInf_le_of_le (k • z) (iInf_le_of_le ((hmem z).mp hz)
          (iInf_le_of_le (k * r) (iInf_le_of_le hr' le_rfl)))
      _ = _ := by
        rw [map_inv_smul_ball μ hk]
        have hrat : (k * r) / (k * ρ) = r / ρ := by field_simp
        rw [hrat]

/-- The normalized ball-mass size in the very-good-annulus event is preserved
by positive spatial dilation. -/
theorem annulusBallMassRatioSize_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (β ρ : ℝ) :
    annulusBallMassSize (μ.map (fun x : ℂ => k⁻¹ • x)) β ρ 0 /
        (μ.map (fun x : ℂ => k⁻¹ • x)) (annulus 0 (ρ / 4) (2 * ρ)) =
      annulusBallMassSize μ β (k * ρ) 0 /
        μ (annulus 0 ((k * ρ) / 4) (2 * (k * ρ))) := by
  have hg : Measurable (fun x : ℂ => k⁻¹ • x) := by fun_prop
  have hs : MeasurableSet (annulus (0 : ℂ) (ρ / 4) (2 * ρ)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  rw [annulusBallMassSize_map_inv_smul μ hk, Measure.map_apply hg hs]
  simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
    preimage_inv_smul_closedBall_zero hk]
  congr 2; ring

end HarmonicBalls

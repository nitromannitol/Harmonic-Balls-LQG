import HarmonicBalls.Steps.Sec11.AnnulusDilation
import HarmonicBalls.Proofs.Sec6.GreenDilation
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-!
# Dilation of annular Green potentials

The planar Green kernel is invariant under positive dilation. The integral
retains the infinite diagonal value in the annular potential.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- A positive dilation sends a ball to the corresponding dilated ball. -/
theorem image_real_smul_ball {k : ℝ} (hk : 0 < k) (z : ℂ) (b : ℝ) :
    (fun x : ℂ => k • x) '' ball z b = ball (k • z) (k * b) := by
  have hmem (x : ℂ) : k • x ∈ ball (k • z) (k * b) ↔ x ∈ ball z b := by
    simp only [mem_ball, dist_smul₀, Real.norm_eq_abs, abs_of_pos hk,
      mul_lt_mul_iff_right₀ hk]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).2 hx
  · intro hy
    refine ⟨k⁻¹ • y, (hmem _).1 ?_, ?_⟩
    · simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hy
    · simp [hk.ne']

/-- The annular Green integral for the inverse-dilated measure equals the
corresponding integral in the original coordinates. -/
theorem annulusGreenIntegral_comp_real_smul
    (μ : Measure ℂ) {k : ℝ} (hk : 0 < k) (z x : ℂ) (a b : ℝ) :
    (∫⁻ y in annulus z a b, (if y = x then ∞ else
      ENNReal.ofReal (greenFunction (ball z b) x y))
      ∂(μ.map (fun y : ℂ => k⁻¹ • y))) =
    ∫⁻ y in annulus (k • z) (k * a) (k * b), (if y = k • x then ∞ else
      ENNReal.ofReal (greenFunction (ball (k • z) (k * b)) (k • x) y)) ∂μ := by
  have hA : MeasurableSet (annulus z a b) := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hf : Measurable (fun y : ℂ => if y = x then ∞ else
      ENNReal.ofReal (greenFunction (ball z b) x y)) :=
    Measurable.ite (measurableSet_singleton x) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  rw [setLIntegral_map hA hf (by fun_prop), preimage_inv_smul_annulus hk]
  apply lintegral_congr_ae
  filter_upwards [] with y
  have heq : k⁻¹ • y = x ↔ y = k • x := by
    constructor
    · intro h
      have h' := congrArg (fun v : ℂ => k • v) h
      simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using h'
    · intro h
      subst y
      simp [hk.ne']
  have hG := greenFunction_dilation (ball z b) isBounded_ball hk x (k⁻¹ • y)
  rw [image_real_smul_ball hk] at hG
  simp only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] at hG
  simp only [heq, hG]

/-- The annular Green-potential supremum scales under positive dilation. -/
theorem annulusGreenPotentialSup_comp_real_smul
    (μ : Measure ℂ) {k : ℝ} (hk : 0 < k) (z : ℂ) (a b : ℝ) :
    annulusGreenPotentialSup (μ.map (fun y : ℂ => k⁻¹ • y)) z a b =
      annulusGreenPotentialSup μ (k • z) (k * a) (k * b) := by
  unfold annulusGreenPotentialSup
  simp_rw [annulusGreenIntegral_comp_real_smul μ hk]
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    exact le_iSup_of_le (k • x) (le_iSup_of_le ((smul_mem_annulus_iff hk z x a b).2 hx) le_rfl)
  · refine iSup_le fun y => iSup_le fun hy => ?_
    have hx : k⁻¹ • y ∈ annulus z a b := by
      apply (smul_mem_annulus_iff hk z (k⁻¹ • y) a b).1
      simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hy
    apply le_iSup_of_le (k⁻¹ • y)
    apply le_iSup_of_le hx
    simp only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
    exact le_rfl

/-- Combining spatial dilation with a positive mass normalization scales the
annular Green-potential supremum by the mass factor. -/
theorem annulusGreenPotentialSup_comp_real_smul_measure
    (μ : Measure ℂ) {k : ℝ} (hk : 0 < k) (c : ℝ≥0∞) (z : ℂ) (a b : ℝ) :
    annulusGreenPotentialSup (c • μ.map (fun y : ℂ => k⁻¹ • y)) z a b =
      c * annulusGreenPotentialSup μ (k • z) (k * a) (k * b) := by
  rw [annulusGreenPotentialSup_smul, annulusGreenPotentialSup_comp_real_smul μ hk]

end HarmonicBalls

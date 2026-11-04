import HarmonicBalls.Steps.Sec11.OdometerScaling

/-!
# Dilation of annular mass and odometer suprema

These pathwise identities are the geometric part of transferring the
unit-disk annular comparison estimates to a disk of radius `k`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- Dilation transports membership of any annulus, including annuli with
nonpositive inner radius. -/
theorem smul_mem_annulus_iff {k : ℝ} (hk : 0 < k) (z x : ℂ) (a b : ℝ) :
    k • x ∈ annulus (k • z) (k * a) (k * b) ↔ x ∈ annulus z a b := by
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos hk, mul_lt_mul_iff_right₀ hk, mul_le_mul_iff_right₀ hk]

/-- The pullback of an annulus under inverse dilation is the corresponding
annulus in the original coordinates. -/
theorem preimage_inv_smul_annulus {k : ℝ} (hk : 0 < k) (z : ℂ) (a b : ℝ) :
    (fun x : ℂ => k⁻¹ • x) ⁻¹' annulus z a b = annulus (k • z) (k * a) (k * b) := by
  ext x
  have h := smul_mem_annulus_iff hk z (k⁻¹ • x) a b
  simpa only [mem_preimage, smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using h.symm

/-- Annular mass intersected with the scaled cluster, under an explicit
measurability hypothesis for that cluster. -/
theorem measure_annulus_inter_cluster_comp_real_smul
    {μ : Measure ℂ} {R k c t : ℝ} {p z : ℂ} {a b : ℝ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hcluster : MeasurableSet (cluster
      (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) R p (c * t))) :
    (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ)
      (annulus z a b ∩ cluster
        (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) R p (c * t)) =
    ENNReal.ofReal c * μ (annulus (k • z) (k * a) (k * b) ∩
      cluster μ (k * R) (k • p) t) := by
  have ha : MeasurableSet (annulus z a b) := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) (ha.inter hcluster),
    preimage_inter, preimage_inv_smul_annulus hk, cluster_comp_real_smul hk hc ht]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_preimage, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]

/-- The annular supremum of the extended unit-disk odometer scales by the
same factor as the measure, when the annulus stays inside the disk away
from the pole. -/
theorem iSup_odometerExt_annulus_comp_real_smul
    {μ : Measure ℂ} {k c t : ℝ} {p z : ℂ} {a b : ℝ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hA : annulus z a b ⊆ ball (0 : ℂ) 1 \ {p}) :
    (⨆ x ∈ annulus z a b, odometerExt
      (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ) p (c * t) x) =
    ENNReal.ofReal c * (⨆ y ∈ annulus (k • z) (k * a) (k * b),
      ENNReal.ofReal (odometer μ k (k • p) t y)) := by
  have hp : ∀ x ∈ annulus z a b,
      odometerExt (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ) p (c * t) x =
        ENNReal.ofReal c * ENNReal.ofReal (odometer μ k (k • p) t (k • x)) := by
    intro x hx
    have hx' := hA hx
    have hxne : x ≠ p := hx'.2
    simpa only [hxne, ↓reduceIte] using
      (odometerExt_comp_real_smul (μ := μ) (p := p) hk hc ht (ball_subset_closedBall hx'.1))
  simp_rw [ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    rw [hp x hx]
    exact le_iSup_of_le (k • x)
      (le_iSup_of_le ((smul_mem_annulus_iff hk z x a b).2 hx) le_rfl)
  · refine iSup_le fun y => iSup_le fun hy => ?_
    have hxy : k⁻¹ • y ∈ annulus z a b := by
      have hh := (smul_mem_annulus_iff hk z (k⁻¹ • y) a b)
      apply hh.mp
      simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hy
    have hv := hp (k⁻¹ • y) hxy
    simp only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] at hv
    rw [← hv]
    exact le_iSup_of_le (k⁻¹ • y) (le_iSup_of_le hxy le_rfl)

/-- A unit-disk annular mass-to-odometer inequality transfers to the
dilated disk with exactly the same constant. -/
theorem annulus_mass_bound_of_scaled_unit_bound
    {μ : Measure ℂ} {k c t : ℝ} {p z : ℂ} {a b A B : ℝ} {C : ℝ≥0∞}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hcluster : MeasurableSet (cluster
      (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) 1 p (c * t)))
    (hA : annulus z A B ⊆ ball (0 : ℂ) 1 \ {p})
    (hunit : (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ)
        (annulus z a b ∩ cluster
          (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) 1 p (c * t)) ≤
      C * (⨆ x ∈ annulus z A B, odometerExt
        (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ) p (c * t) x)) :
    μ (annulus (k • z) (k * a) (k * b) ∩ cluster μ k (k • p) t) ≤
      C * (⨆ y ∈ annulus (k • z) (k * A) (k * B), ENNReal.ofReal (odometer μ k (k • p) t y)) := by
  rw [measure_annulus_inter_cluster_comp_real_smul hk hc ht hcluster,
    iSup_odometerExt_annulus_comp_real_smul hk hc ht hA, mul_one] at hunit
  rw [mul_left_comm C (ENNReal.ofReal c)] at hunit
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hc0 hcT).mp (by simpa only [mul_comm] using hunit)

end HarmonicBalls

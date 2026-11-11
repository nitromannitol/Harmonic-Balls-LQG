import HarmonicBalls.Proofs.Sec5.AreaPunctureObstruction
import HarmonicBalls.Proofs.Sec5.LaplacianScaling
import HarmonicBalls.Proofs.Sec5.RestrictedClusterLocality

/-! # Inadmissibility for every positive multiple of area measure -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- For any positive multiple of area measure, a negative bump can be scaled
into a disc supersolution at any positive time. -/
theorem exists_area_supersolution_neg_at_of_pos
    {R t C : ℝ} {z a : ℂ} (hz : z ∈ ball (0 : ℂ) R)
    (ha : a ∈ ball (0 : ℂ) R) (haz : a ≠ z) (ht : 0 < t) (hC : 0 < C) :
    ∃ w : ℂ → ℝ, w ∈ supersolutions (ENNReal.ofReal C • volume) R z t ∧ w a < 0 := by
  obtain ⟨D, hD, w, hw, hwneg⟩ := exists_area_supersolution_neg_at hz ha haz ht
  let c := min 1 (C / D)
  have hc : 0 < c := lt_min (by norm_num) (div_pos hC hD)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcD : c * D ≤ C := by
    have h := mul_le_mul_of_nonneg_right (min_le_right 1 (C / D)) hD.le
    simpa [div_mul_cancel₀ C hD.ne'] using h
  have hμ : ENNReal.ofReal c • (ENNReal.ofReal D • volume : Measure ℂ) ≤
      ENNReal.ofReal C • volume := by
    rw [smul_smul, ← ENNReal.ofReal_mul hc.le]
    gcongr
  refine ⟨fun x => c * w x, ⟨hw.1.const_mul c, (hw.2.1.const_mul hc).mono_measure hμ, ?_⟩, ?_⟩
  · intro x hx hxz
    have hG := greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := R)) z x
    have hscale := mul_le_mul_of_nonneg_left (hw.2.2 x hx hxz) hc.le
    have hct : c * t ≤ t := by nlinarith
    have hobs := mul_le_mul_of_nonneg_right hct hG
    nlinarith
  · exact mul_neg_of_pos_of_neg hc hwneg

/-- The closure-defined pointwise infimum on a punctured disc is inadmissible
for every positive multiple of planar area measure and every positive time. -/
theorem area_punctured_disc_infimum_not_admissible
    {R t C : ℝ} {z a : ℂ} (ha : a ∈ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) (hC : 0 < C) :
    leastSupersolutionOn (ENNReal.ofReal C • volume) (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn (ENNReal.ofReal C • volume) (ball (0 : ℂ) R \ {a}) z t := by
  have haz : a ≠ z := Ne.symm (by simpa using hz.2)
  obtain ⟨w, hw, hn⟩ := exists_area_supersolution_neg_at_of_pos hz.1 ha haz ht hC
  exact leastSupersolutionOn_punctured_disc_not_mem_of_negative ha hz ht.le hw hn

/-- In particular, ordinary planar area measure gives an obstruction. -/
theorem volume_punctured_disc_infimum_not_admissible
    {R t : ℝ} {z a : ℂ} (ha : a ∈ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) :
    leastSupersolutionOn volume (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn volume (ball (0 : ℂ) R \ {a}) z t := by
  simpa using area_punctured_disc_infimum_not_admissible ha hz ht (C := 1) (by norm_num)

/-- The same obstruction holds for any measure that dominates a positive
multiple of area measure. -/
theorem punctured_disc_infimum_not_admissible_of_area_lower_bound
    {μ : Measure ℂ} {R t C : ℝ} {z a : ℂ} (ha : a ∈ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) (hC : 0 < C)
    (hμ : ENNReal.ofReal C • volume ≤ μ) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t := by
  have haz : a ≠ z := Ne.symm (by simpa using hz.2)
  obtain ⟨w, hw, hn⟩ := exists_area_supersolution_neg_at_of_pos hz.1 ha haz ht hC
  exact leastSupersolutionOn_punctured_disc_not_mem_of_negative ha hz ht.le
    (supersolutions_mono_measure hμ hw) hn


end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.SmoothLaplacianBound
import HarmonicBalls.Proofs.Sec5.PuncturedDiscCompetitors

/-! # A puncture obstruction for a multiple of area measure -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff

/-- A smooth negative bump away from the pole is a disc supersolution for
some constant multiple of area measure. -/
theorem exists_area_supersolution_neg_at
    {R t : ℝ} {z a : ℂ} (hz : z ∈ ball (0 : ℂ) R)
    (ha : a ∈ ball (0 : ℂ) R) (haz : a ≠ z) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∃ w : ℂ → ℝ,
      w ∈ supersolutions (ENNReal.ofReal C • volume) R z t ∧ w a < 0 := by
  have hg : 0 < greenFunction (ball 0 R) z a := greenFunction_ball_pos hz ha haz.symm
  have hc := (continuousOn_greenFunction_ball hz).continuousAt
    (isOpen_compl_singleton.mem_nhds haz)
  have hn : {x : ℂ | greenFunction (ball 0 R) z a / 2 <
      greenFunction (ball 0 R) z x} ∈ 𝓝 a :=
    hc (Ioi_mem_nhds (by linarith))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hn
  let b : ContDiffBump a := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let k : ℝ := t * (greenFunction (ball 0 R) z a / 2)
  have hk : 0 < k := by dsimp [k]; positivity
  let w : ℂ → ℝ := fun x => -k * b x
  have hw : ContDiff ℝ ∞ w := contDiff_const.mul b.contDiff
  have hwc : HasCompactSupport w := b.hasCompactSupport.mul_left
  obtain ⟨C, hC, hΔ⟩ := exists_laplacianLE_smooth_compactSupport hw hwc
  refine ⟨C, hC, w, ⟨hw.continuous.continuousOn, hΔ _, ?_⟩, ?_⟩
  · intro x hx hxz
    by_cases hxb : x ∈ ball a r
    · have hxg := hrsub hxb
      have hb : b x ≤ 1 := b.le_one
      have hkg : k ≤ t * greenFunction (ball 0 R) z x :=
        mul_le_mul_of_nonneg_left hxg.le ht.le
      have hkb : k * b x ≤ k := by
        simpa using mul_le_mul_of_nonneg_left hb hk.le
      change -t * greenFunction (ball 0 R) z x ≤ -k * b x
      linarith
    · have hxnot : x ∉ tsupport (b : ℂ → ℝ) := by
        rw [b.tsupport_eq]
        exact fun hx => hxb (Metric.closedBall_subset_ball (by dsimp [b]; linarith) hx)
      have hb : b x = 0 := image_eq_zero_of_notMem_tsupport hxnot
      dsimp [w]
      rw [hb, mul_zero]
      have hG := greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := R)) z x
      nlinarith
  · dsimp [w]
    have hb : b a = 1 := b.one_of_mem_closedBall (by simp [b]; positivity)
    rw [hb, mul_one]
    linarith

/-- For every positive time, some multiple of area measure makes the
punctured-disc least supersolution inadmissible. -/
theorem exists_area_punctured_disc_infimum_not_admissible
    {R t : ℝ} {z a : ℂ} (ha : a ∈ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
      leastSupersolutionOn (ENNReal.ofReal C • volume) (ball (0 : ℂ) R \ {a}) z t ∉
        supersolutionsOn (ENNReal.ofReal C • volume) (ball (0 : ℂ) R \ {a}) z t := by
  have haz : a ≠ z := Ne.symm (by simpa using hz.2)
  obtain ⟨C, hC, w, hw, hn⟩ := exists_area_supersolution_neg_at hz.1 ha haz ht
  exact ⟨C, hC, leastSupersolutionOn_punctured_disc_not_mem_of_negative ha hz ht.le hw hn⟩

#print axioms exists_area_supersolution_neg_at
#print axioms exists_area_punctured_disc_infimum_not_admissible

end HarmonicBalls

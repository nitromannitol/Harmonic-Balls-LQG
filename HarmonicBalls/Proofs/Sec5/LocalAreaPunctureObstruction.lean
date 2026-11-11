import HarmonicBalls.Proofs.Sec5.AreaPunctureAllDensities
import HarmonicBalls.Proofs.Sec5.GeneralDomainMeasureLocality
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-! # Puncture obstruction from a local area lower bound -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff

/-- A local area lower bound near the puncture supplies a negative disc
supersolution, with no condition on the measure away from that neighborhood. -/
theorem exists_disc_supersolution_neg_of_local_area_lower_bound
    {μ : Measure ℂ} {R t C : ℝ} {z a : ℂ} {V : Set ℂ}
    (hz : z ∈ ball (0 : ℂ) R) (ha : a ∈ ball (0 : ℂ) R) (haz : a ≠ z)
    (ht : 0 < t) (hC : 0 < C) (hV : IsOpen V) (haV : a ∈ V)
    (hμ : (ENNReal.ofReal C • volume).restrict V ≤ μ) :
    ∃ w : ℂ → ℝ, w ∈ supersolutions μ R z t ∧ w a < 0 := by
  have hg : 0 < greenFunction (ball 0 R) z a := greenFunction_ball_pos hz ha haz.symm
  have hc := (continuousOn_greenFunction_ball hz).continuousAt
    (isOpen_compl_singleton.mem_nhds haz)
  have hn : {x : ℂ | greenFunction (ball 0 R) z a / 2 <
      greenFunction (ball 0 R) z x} ∈ 𝓝 a := hc (Ioi_mem_nhds (by linarith))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hn (hV.mem_nhds haV))
  let b : ContDiffBump a := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbV : tsupport (b : ℂ → ℝ) ⊆ V := by
    rw [b.tsupport_eq]
    exact fun x hx => (hrsub (Metric.closedBall_subset_ball (by dsimp [b]; linarith) hx)).2
  let k : ℝ := t * (greenFunction (ball 0 R) z a / 2)
  have hk : 0 < k := by dsimp [k]; positivity
  let f : ℂ → ℝ := fun x => -k * b x
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul b.contDiff
  have hfc : HasCompactSupport f := b.hasCompactSupport.mul_left
  obtain ⟨D, hD, hΔ⟩ := exists_laplacianLE_smooth_compactSupport hf hfc
  let c := min 1 (C / D)
  have hcp : 0 < c := lt_min (by norm_num) (div_pos hC hD)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcD : c * D ≤ C := by
    have h := mul_le_mul_of_nonneg_right (min_le_right 1 (C / D)) hD.le
    simpa [div_mul_cancel₀ C hD.ne'] using h
  let w : ℂ → ℝ := fun x => c * f x
  have hmass : ENNReal.ofReal c • (ENNReal.ofReal D • volume : Measure ℂ) ≤
      ENNReal.ofReal C • volume := by
    rw [smul_smul, ← ENNReal.ofReal_mul hcp.le]
    gcongr
  have hΔglobal : LaplacianLE w (ENNReal.ofReal C • volume) V :=
    ((hΔ V).const_mul hcp).mono_measure hmass
  have hrestrict : LaplacianLE w ((ENNReal.ofReal C • volume).restrict V) V := by
    apply (laplacianLE_iff_of_restrict_eq hV.measurableSet ?_ w).mp hΔglobal
    simp [Measure.restrict_restrict hV.measurableSet]
  have hΔV : LaplacianLE w μ V := hrestrict.mono_measure hμ
  have hΔoutside : LaplacianLE w μ (tsupport (b : ℂ → ℝ))ᶜ := by
    apply (laplacianLE_zero μ _).congr_eqOn (isClosed_tsupport (b : ℂ → ℝ)).isOpen_compl.measurableSet
    intro x hx
    have hb : b x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [w, f, hb]
  have hcover : ball (0 : ℂ) R ⊆ V ∪ (tsupport (b : ℂ → ℝ))ᶜ := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact Or.inl hxV
    · exact Or.inr (fun h => hxV (hbV h))
  have hΔw : LaplacianLE w μ (ball 0 R) :=
    (hΔV.union hV (isClosed_tsupport (b : ℂ → ℝ)).isOpen_compl hΔoutside).mono_set hcover
  refine ⟨w, ⟨(continuous_const.mul hf.continuous).continuousOn, hΔw, ?_⟩, ?_⟩
  · intro x hx hxz
    have hfobs : -t * greenFunction (ball 0 R) z x ≤ f x := by
      by_cases hxb : x ∈ ball a r
      · have hxg := (hrsub hxb).1
        have hb : b x ≤ 1 := b.le_one
        have hkg : k ≤ t * greenFunction (ball 0 R) z x :=
          mul_le_mul_of_nonneg_left hxg.le ht.le
        have hkb : k * b x ≤ k := by simpa using mul_le_mul_of_nonneg_left hb hk.le
        change -t * greenFunction (ball 0 R) z x ≤ -k * b x
        linarith
      · have hxnot : x ∉ tsupport (b : ℂ → ℝ) := by
          rw [b.tsupport_eq]
          exact fun hx => hxb (Metric.closedBall_subset_ball (by dsimp [b]; linarith) hx)
        have hb : b x = 0 := image_eq_zero_of_notMem_tsupport hxnot
        dsimp [f]
        rw [hb, mul_zero]
        have hG := greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := R)) z x
        nlinarith
    have hG := greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := R)) z x
    have hscaled := mul_le_mul_of_nonneg_left hfobs hcp.le
    have hct : c * t ≤ t := by nlinarith
    have hobs := mul_le_mul_of_nonneg_right hct hG
    dsimp [w]
    nlinarith
  · have hb : b a = 1 := b.one_of_mem_closedBall (by simp [b]; positivity)
    dsimp [w, f]
    rw [hb, mul_one]
    exact mul_neg_of_pos_of_neg hcp (neg_neg_of_pos hk)

/-- A punctured-disc pointwise infimum is inadmissible whenever the measure
locally dominates a positive multiple of planar area near the puncture. -/
theorem punctured_disc_infimum_not_admissible_of_local_area_lower_bound
    {μ : Measure ℂ} {R t C : ℝ} {z a : ℂ} {V : Set ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t) (hC : 0 < C) (hV : IsOpen V) (haV : a ∈ V)
    (hμ : (ENNReal.ofReal C • volume).restrict V ≤ μ) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t := by
  have haz : a ≠ z := Ne.symm (by simpa using hz.2)
  obtain ⟨w, hw, hn⟩ := exists_disc_supersolution_neg_of_local_area_lower_bound
    hz.1 ha haz ht hC hV haV hμ
  exact leastSupersolutionOn_punctured_disc_not_mem_of_negative ha hz ht.le hw hn

end HarmonicBalls

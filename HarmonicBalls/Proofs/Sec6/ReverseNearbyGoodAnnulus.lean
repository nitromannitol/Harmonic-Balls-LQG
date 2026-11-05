import HarmonicBalls.Proofs.Sec6.ReverseAnnulusWitnessMass
import HarmonicBalls.Proofs.Sec6.ReverseCollarReturn
import HarmonicBalls.Proofs.Sec6.UniformTranslatedCircleCrossing

/-! # Reverse stability of good annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology

/-- A good nearby annulus yields a good reference annulus after relaxation
of both thresholds. The displacement is chosen independently of the nearby
centre and its witnesses. -/
theorem exists_reverse_nearby_goodAnnulus_of_slack
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ)
    {r a a' amid b b' : ℝ} (hr : 0 < r)
    (hnull3 : μ (sphere z (3*r)) = 0) (hnull5 : μ (sphere z (5*r)) = 0)
    (hpos : 0 < μ (annulus z (3*r) (5*r)))
    (hfin : μ (annulus z (3*r) (5*r)) ≠ ∞)
    (hamid : ENNReal.ofReal a' < ENNReal.ofReal amid)
    (haa : ENNReal.ofReal amid < ENNReal.ofReal a)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (hbudget : ENNReal.ofReal b + 2*ε + ε ≤ ENNReal.ofReal b') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      IsGoodAnnulus μ r w a b → IsGoodAnnulus μ r z a' b' := by
  let A := annulus z (3*r) (5*r)
  let K := sphere z (4*r)
  have hK : IsCompact K := isCompact_sphere z (4*r)
  have hKA : K ⊆ A := by
    intro u hu
    simp only [K, mem_sphere] at hu
    simp only [A, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    rw [hu]
    constructor <;> linarith
  obtain ⟨η, δm, hδm, hδη, hmass⟩ :=
    exists_reverse_nearby_annulus_collar_witness_mass_transfer μ z (3*r) (5*r)
      hnull3 hnull5 hpos hfin hamid ENNReal.ofReal_ne_top
  have hη : 0 < η := hδm.trans hδη
  obtain ⟨δc, hδc, hcompare⟩ := exists_uniform_reverse_nearby_annulus_avoidance_comparison
    (z := z) (r := 3*r) (R := 5*r) (s := 3*r+η) (S := 5*r-η)
    (by positivity) (by linarith) (by linarith) (by linarith) hK hKA hε
  obtain ⟨δs, hδs, hstart⟩ := uniform_goodAnnulus_avoidance_near_translated_circle hr hε
  obtain ⟨d, hdpos, hdlt⟩ := exists_between hpos
  obtain ⟨δp, hδp, hp⟩ := exists_nearby_annulus_symmDiff_mass_lt μ z (3*r) (5*r)
    hnull3 hnull5 hdpos
  let δ := min δm (min δc (min δs (min δp (r/2))))
  refine ⟨δ, lt_min hδm (lt_min hδc (lt_min hδs (lt_min hδp (by positivity)))), ?_⟩
  intro w hw hg Y hY hYsub hYmass u hu
  have hwm : dist w z < δm := hw.trans_le (min_le_left _ _)
  have hwc : dist w z < δc := hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hws : dist w z < δs := hw.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hwp : dist w z < δp := hw.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hwr : dist w z < r/2 := hw.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  let B := annulus w (3*r) (5*r)
  let C : Set ℂ := {q | 3*r+η ≤ dist q z ∧ dist q z ≤ 5*r-η}
  let X := (B ∩ Y) ∪ (B \ C)
  have hC : IsClosed C := (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
    (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hB : MeasurableSet B := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hX : MeasurableSet X := (hB.inter hY).union (hB.diff hC.measurableSet)
  have hXB : X ⊆ B := by intro q hq; rcases hq with hq | hq <;> exact hq.1
  have hsub : X ⊆ (B ∩ Y) ∪ (B \ annulus z (3*r+η) (5*r-η)) := by
    intro q hq
    rcases hq with hq | ⟨hq, hn⟩
    · exact Or.inl hq
    · right; refine ⟨hq, ?_⟩
      intro hq'
      apply hn
      simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hq'
      exact ⟨hq'.2.le, hq'.1.le⟩
  have hXm : μ X ≤ ENNReal.ofReal amid * μ B :=
    (measure_mono hsub).trans (hmass w hwm Y hYmass)
  have hBfin : μ B ≠ ∞ := measure_ne_top_of_subset (show B ⊆ ball w (5*r) from sdiff_subset)
    (measure_ball_ne_top (μ := μ))
  have hBpos : 0 < μ B := by
    by_contra hn
    have hzero : μ B = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hdiff : μ (A \ B) < d := (measure_mono
      (subset_union_left : A \ B ⊆ (A \ B) ∪ (B \ A))).trans_lt (hp w hwp)
    have hcover : A ⊆ B ∪ (A \ B) := by intro q hq; by_cases h : q ∈ B <;> simp_all
    have hle : μ A ≤ μ B + μ (A \ B) := (measure_mono hcover).trans (measure_union_le _ _)
    rw [hzero, zero_add] at hle
    exact (not_lt_of_ge (hdlt.trans_le hle).le) hdiff
  have hXmlt : μ X < ENNReal.ofReal a * μ B :=
    hXm.trans_lt (ENNReal.mul_lt_mul_left hBpos.ne' hBfin haa)
  let v := u + (w-z)
  have huv : dist u v = dist w z := by
    simp only [v, dist_eq_norm]
    change ‖u - (u + (w-z))‖ = ‖w-z‖
    rw [show u - (u + (w-z)) = -(w-z) by abel, norm_neg]
  have hv : v ∈ sphere w (4*r) := by
    rw [mem_sphere] at hu ⊢
    simpa only [v, dist_eq_norm, show u + (w-z) - w = u-z by abel] using hu
  have huB : u ∈ B := by
    have ht := dist_triangle u z w
    have ht' := dist_triangle u w z
    have hu' := mem_sphere.mp hu
    simp only [B, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith [dist_comm w z]
  have hbound := hstart μ w a b hBfin hg u v hv (by rw [huv]; exact hws) huB X hX hXB hXmlt
  have hcomp := hcompare w hwc u hu Y
  exact hcomp.trans ((add_le_add hbound le_rfl).trans hbudget)

end HarmonicBalls.Section6

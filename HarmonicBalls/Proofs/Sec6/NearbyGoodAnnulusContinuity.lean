import HarmonicBalls.Proofs.Sec6.NearbyAnnulusCompactWitness

/-! # Stability of good annuli under displacement of the centre -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology

/-- A good annulus remains good at nearby centres after relaxing both thresholds.
The displacement is uniform over all measurable witnesses and starting points. -/
theorem exists_nearby_goodAnnulus_of_slack
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ)
    {r a a' amid b b' : ℝ} (hr : 0 < r)
    (hnull3 : μ (sphere z (3 * r)) = 0) (hnull5 : μ (sphere z (5 * r)) = 0)
    (hpos : 0 < μ (annulus z (3 * r) (5 * r)))
    (hfin : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hamid : ENNReal.ofReal a' < ENNReal.ofReal amid)
    (haa : ENNReal.ofReal amid < ENNReal.ofReal a)
    (hg : IsGoodAnnulus μ r z a b) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hbudget : ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → IsGoodAnnulus μ r w a' b' := by
  let A := annulus z (3 * r) (5 * r)
  let K : Set ℂ := {q | (7 / 2 : ℝ) * r ≤ dist q z ∧ dist q z ≤ (9 / 2 : ℝ) * r}
  have hKclosed : IsClosed K := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const) |>.inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hK : IsCompact K := (isCompact_closedBall z ((9 / 2 : ℝ) * r)).of_isClosed_subset
    hKclosed (by intro q hq; exact mem_closedBall.mpr hq.2)
  have hKA : K ⊆ A := by
    intro q hq
    simp only [A, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith [hq.1, hq.2]
  obtain ⟨η, δm, hδm, hδη, hmass⟩ :=
    exists_nearby_annulus_collar_witness_mass_transfer μ z (3*r) (5*r)
      hnull3 hnull5 hpos hfin hamid ENNReal.ofReal_ne_top
  have hη : 0 < η := hδm.trans hδη
  obtain ⟨δc, hδc, hcompare⟩ := exists_uniform_nearby_annulus_avoidance_comparison
    (z := z) (r := 3*r) (R := 5*r) (s := 3*r+η) (S := 5*r-η)
    (by positivity) (by linarith) (by linarith) (by linarith) hK hKA hε
  obtain ⟨δs, hδs, hstart⟩ := IsGoodAnnulus.uniform_avoidance_near_circle hr hfin hg hε
  let δ := min δm (min δc (min δs (r / 2)))
  refine ⟨δ, lt_min hδm (lt_min hδc (lt_min hδs (by positivity))), ?_⟩
  intro w hw Y hY hYsub hYmass u hu
  have hwm : dist w z < δm := hw.trans_le (min_le_left _ _)
  have hwc : dist w z < δc := hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hws : dist w z < δs := hw.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hwr : dist w z < r / 2 := hw.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hu' : dist u w = 4*r := mem_sphere.mp hu
  have hut := dist_triangle u w z
  have hwt := dist_triangle u z w
  have hdu : dist u z ≤ (9/2 : ℝ)*r := by linarith
  have hdl : (7/2 : ℝ)*r ≤ dist u z := by linarith [dist_comm z w]
  have huK : u ∈ K := ⟨hdl, hdu⟩
  let v := u + (z - w)
  have hvdist : dist v z = dist u w := by
    simp only [v, dist_eq_norm]
    change ‖u + (z - w) - z‖ = ‖u - w‖
    exact congrArg norm (show u + (z - w) - z = u - w by abel)
  have hv : v ∈ sphere z (4*r) := by rw [mem_sphere, hvdist, hu']
  have huv : dist u v = dist w z := by
    simp only [v, dist_eq_norm]
    change ‖u - (u + (z - w))‖ = ‖w - z‖
    exact congrArg norm (show u - (u + (z - w)) = w - z by abel)
  let C : Set ℂ := {q | 3*r+η ≤ dist q z ∧ dist q z ≤ 5*r-η}
  let X := (A ∩ Y) ∪ (A \ C)
  have hC : IsClosed C := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const) |>.inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hX : MeasurableSet X := (hA.inter hY).union (hA.diff hC.measurableSet)
  have hXA : X ⊆ A := by intro q hq; rcases hq with hq | hq <;> exact hq.1
  have hsub : X ⊆ (A ∩ Y) ∪ (A \ annulus z (3*r+η) (5*r-η)) := by
    intro q hq
    rcases hq with hq | ⟨hq, hn⟩
    · exact Or.inl hq
    · right; refine ⟨hq, ?_⟩
      intro hq'
      apply hn
      simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hq'
      exact ⟨hq'.2.le, hq'.1.le⟩
  have hXm : μ X ≤ ENNReal.ofReal amid * μ A :=
    (measure_mono hsub).trans ((hmass w hwm).2 Y hYmass)
  have hXmlt : μ X < ENNReal.ofReal a * μ A :=
    hXm.trans_lt (ENNReal.mul_lt_mul_left hpos.ne' hfin haa)
  have hbound := hstart u v hv (by rw [huv]; exact hws) (hKA huK) X hX hXA hXmlt
  have hcomp := hcompare w hwc u huK Y
  calc
    _ ≤ _ + ε := hcomp
    _ ≤ (ENNReal.ofReal b + 2 * ε) + ε := add_le_add hbound le_rfl
    _ ≤ _ := hbudget

end HarmonicBalls.Section6

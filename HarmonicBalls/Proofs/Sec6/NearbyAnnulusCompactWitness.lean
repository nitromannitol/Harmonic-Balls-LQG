import HarmonicBalls.Proofs.Sec6.NearbyAnnulusCollar
import HarmonicBalls.Proofs.Sec6.CircleCrossingProbability
import HarmonicBalls.Proofs.Sec6.UniformCollarReturn
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-! # Compact obstacles for annular witness transfer -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology

/-- A measurable witness with strict mass slack can be enlarged to the
complement of a compact obstacle, retaining the mass bound. -/
theorem exists_compact_obstacle_of_witness_mass_lt
    (μ : Measure ℂ) {A X : Set ℂ} (hA : MeasurableSet A) (hX : MeasurableSet X)
    (hfin : μ A ≠ ∞) {m : ℝ≥0∞} (hm : μ X < m) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ A \ X ∧ μ (A \ K) ≤ m := by
  obtain ⟨δ, hδ, hδm⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hm
  have hAX : MeasurableSet (A \ X) := hA.diff hX
  have hAXfin : μ (A \ X) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)
  obtain ⟨K, hKsub, hK, hKmass⟩ := hAX.exists_isCompact_sdiff_lt hAXfin (by exact ENNReal.coe_ne_zero.mpr hδ.ne')
  refine ⟨K, hK, hKsub, ?_⟩
  have hcover : A \ K ⊆ X ∪ ((A \ X) \ K) := by
    intro x hx
    by_cases hxX : x ∈ X
    · exact Or.inl hxX
    · exact Or.inr ⟨⟨hx.1, hxX⟩, hx.2⟩
  calc
    μ (A \ K) ≤ μ (X ∪ ((A \ X) \ K)) := measure_mono hcover
    _ ≤ μ X + μ ((A \ X) \ K) := measure_union_le _ _
    _ ≤ μ X + (δ : ℝ≥0∞) := add_le_add le_rfl hKmass.le
    _ ≤ m := hδm.le

/-- Until domain exit, avoiding a set is equivalent to staying in the
domain with that set removed. -/
theorem avoid_eq_stay_sdiff (A K : Set ℂ) :
    {ω : ContinuousPath ℂ | ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime Kᶜ ω} =
      {ω | ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime (A \ K) ω} := by
  ext ω
  constructor
  · intro h
    change ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime (A \ K) ω
    rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    by_cases ha : ω t ∈ A
    · have hk : ω t ∈ K := by
        by_contra hn
        exact ht ⟨ha, hn⟩
      exact h.trans (ContinuousPath.exitTime_le_of_notMem Kᶜ ω t (by simpa using hk))
    · exact ContinuousPath.exitTime_le_of_notMem A ω t ha
  · intro h
    exact h.trans (ContinuousPath.exitTime_mono (by intro x hx; exact hx.2) ω)

/-- The good-annulus condition bounds avoidance of any compact obstacle
whose complement in the annulus has sufficiently small mass. -/
theorem IsGoodAnnulus.avoid_compact_le
    {μ : Measure ℂ} {z : ℂ} {r a b : ℝ} (hg : IsGoodAnnulus μ r z a b)
    {K : Set ℂ} (hK : IsCompact K)
    (hm : μ (annulus z (3 * r) (5 * r) \ K) ≤
      ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)))
    {y : ℂ} (hy : y ∈ sphere z (4 * r)) :
    planarBrownianMotion y {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
      ContinuousPath.exitTime Kᶜ ω} ≤ ENNReal.ofReal b := by
  rw [avoid_eq_stay_sdiff]
  exact hg _ ((isOpen_ball.sdiff isClosed_closedBall).measurableSet.diff hK.isClosed.measurableSet)
    sdiff_subset hm y hy

/-- Good-annulus avoidance bounds extend uniformly to nearby starting points
for every measurable witness with strict mass slack. -/
theorem IsGoodAnnulus.uniform_avoidance_near_circle
    {μ : Measure ℂ} {z : ℂ} {r a b : ℝ} (hr : 0 < r)
    (hfin : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hg : IsGoodAnnulus μ r z a b) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℂ, y ∈ sphere z (4 * r) → dist x y < δ →
      x ∈ annulus z (3 * r) (5 * r) → ∀ X : Set ℂ, MeasurableSet X →
      X ⊆ annulus z (3 * r) (5 * r) →
      μ X < ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
      planarBrownianMotion x {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
        ContinuousPath.exitTime X ω} ≤ ENNReal.ofReal b + 2 * ε := by
  let A := annulus z (3 * r) (5 * r)
  have hA : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAb : Bornology.IsBounded A := isBounded_ball.subset sdiff_subset
  have hSA : sphere z (4 * r) ⊆ A := by
    intro x hx
    simp only [mem_sphere] at hx
    simp only [A, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    rw [hx]
    constructor <;> linarith
  obtain ⟨δ, hδ, hnear⟩ := uniform_planarBrownian_exit_before_circle_of_compact
    (show 0 < 4 * r by positivity) hA (isCompact_sphere z (4 * r)) subset_rfl hSA hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hy hxy hx X hX hXA hm
  obtain ⟨K, hK, hKsub, hKm⟩ := exists_compact_obstacle_of_witness_mass_lt μ
    hA.measurableSet hX hfin hm
  have hXK : X ⊆ Kᶜ := by
    intro q hq hk
    exact (hKsub hk).2 hq
  have hbound (v : ℂ) (hv : v ∈ sphere z (4 * r)) :
      planarBrownianMotion v {ω | ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime Kᶜ ω} ≤
        ENNReal.ofReal b := IsGoodAnnulus.avoid_compact_le hg hK hKm hv
  have havoid : planarBrownianMotion x {ω | ContinuousPath.exitTime A ω ≤
      ContinuousPath.exitTime Kᶜ ω} ≤ ENNReal.ofReal b + 2 * ε := by
    by_cases hxs : x ∈ sphere z (4 * r)
    · exact (hbound x hxs).trans (le_add_right le_rfl)
    · have hE := measurableSet_avoid_before_exit hA hK
      have hcomp := planarBrownian_avoidance_le_of_circle_hitting hA hAb hE
        (show x ∈ A \ sphere z (4 * r) from ⟨hx, hxs⟩) (ENNReal.ofReal b) hbound
      apply hcomp.trans
      gcongr
      exact (hnear x y hy hxy).le
  apply (measure_mono ?_).trans havoid
  intro ω hω
  exact hω.trans (ContinuousPath.exitTime_mono hXK ω)

end HarmonicBalls.Section6

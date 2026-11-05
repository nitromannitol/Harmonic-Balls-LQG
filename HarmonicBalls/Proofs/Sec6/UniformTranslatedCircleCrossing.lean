import HarmonicBalls.Proofs.Sec6.CircleCrossingProbability
import HarmonicBalls.Proofs.Sec6.GoodAnnulusSpatialMap
import HarmonicBalls.Proofs.Sec6.NearbyAnnulusCompactWitness

/-! # Translation-uniform Brownian circle crossing -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology

/-- The exit-before-circle estimate for a concentric annulus has a modulus
independent of its centre. -/
theorem uniform_planarBrownian_exit_before_translated_circle
    {r : ℝ} (hr : 0 < r) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w x y : ℂ, y ∈ sphere w (4*r) → dist x y < δ →
      planarBrownianMotion x {ω | ContinuousPath.exitTime (annulus w (3*r) (5*r)) ω ≤
        ContinuousPath.exitTime (annulus w (3*r) (5*r) \ sphere w (4*r)) ω} < ε := by
  let A := annulus (0 : ℂ) (3*r) (5*r)
  let S := sphere (0 : ℂ) (4*r)
  have hSA : S ⊆ A := by
    intro x hx
    simp only [S, mem_sphere] at hx
    simp only [A, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    rw [hx]
    constructor <;> linarith
  obtain ⟨δ, hδ, hb⟩ := uniform_planarBrownian_exit_before_circle_of_compact
    (show 0 < 4*r by positivity) (show IsOpen A from isOpen_ball.sdiff isClosed_closedBall)
    (isCompact_sphere 0 (4*r)) (subset_rfl) hSA hε
  refine ⟨δ, hδ, ?_⟩
  intro w x y hy hxy
  let f : ℂ ≃ₜ ℂ := Homeomorph.addRight w
  have hA : f '' A = annulus w (3*r) (5*r) := by
    have hm (u : ℂ) : u + w ∈ annulus w (3*r) (5*r) ↔ u ∈ A := by
      simp only [A, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
        sub_zero, add_sub_cancel_right]
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hm u).mpr hu
    · intro hv
      refine ⟨v-w, (hm (v-w)).mp ?_, by simp [f]⟩
      simpa only [sub_add_cancel] using hv
  have hS : f '' S = sphere w (4*r) := by
    have hm (u : ℂ) : u + w ∈ sphere w (4*r) ↔ u ∈ S := by
      simp only [S, mem_sphere, dist_eq_norm, sub_zero, add_sub_cancel_right]
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hm u).mpr hu
    · intro hv
      refine ⟨v-w, (hm (v-w)).mp ?_, by simp [f]⟩
      simpa only [sub_add_cancel] using hv
  have hpath : (planarBrownianMotion (x-w)).map (spacetimePathHomeomorph f 1 zero_lt_one) =
      planarBrownianMotion x := by
    have hp := planarBrownianMotion_map_add_from (x-w) w
    have hf : spacetimePathHomeomorph f 1 zero_lt_one =
        (Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight w) := by
      ext ω t
      simp only [spacetimePathHomeomorph_apply, one_mul]
      rfl
    rw [hf]
    simpa only [sub_add_cancel] using hp
  have heq := measure_exitTime_order_eq_of_spacetime_homeomorph f A (A \ S) 1 zero_lt_one
    (planarBrownianMotion (x-w)) (planarBrownianMotion x) hpath
  rw [image_sdiff f.injective, hA, hS] at heq
  rw [heq]
  apply hb (x-w) (y-w)
  · have : y-w ∈ f ⁻¹' (sphere w (4*r)) := by simpa [f] using hy
    simpa only [← hS, preimage_image_eq _ f.injective] using this
  · simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hxy

/-- The starting-point avoidance estimate has a modulus independent of the
centre, measure, good-annulus witness and thresholds. -/
theorem uniform_goodAnnulus_avoidance_near_translated_circle
    {r : ℝ} (hr : 0 < r) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure ℂ) (w : ℂ) (a b : ℝ),
      μ (annulus w (3*r) (5*r)) ≠ ∞ → IsGoodAnnulus μ r w a b →
      ∀ x y : ℂ, y ∈ sphere w (4*r) → dist x y < δ →
      x ∈ annulus w (3*r) (5*r) → ∀ X : Set ℂ, MeasurableSet X →
      X ⊆ annulus w (3*r) (5*r) →
      μ X < ENNReal.ofReal a * μ (annulus w (3*r) (5*r)) →
      planarBrownianMotion x {ω | ContinuousPath.exitTime (annulus w (3*r) (5*r)) ω ≤
        ContinuousPath.exitTime X ω} ≤ ENNReal.ofReal b + 2 * ε := by
  obtain ⟨δ, hδ, hnear⟩ := uniform_planarBrownian_exit_before_translated_circle hr hε
  refine ⟨δ, hδ, ?_⟩
  intro μ w a b hfin hg x y hy hxy hx X hX hXA hm
  let A := annulus w (3*r) (5*r)
  have hA : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAb : Bornology.IsBounded A := isBounded_ball.subset sdiff_subset
  obtain ⟨K, hK, hKsub, hKm⟩ := exists_compact_obstacle_of_witness_mass_lt μ
    hA.measurableSet hX hfin hm
  have hXK : X ⊆ Kᶜ := by
    intro q hq hk
    exact (hKsub hk).2 hq
  have hbound (v : ℂ) (hv : v ∈ sphere w (4*r)) :
      planarBrownianMotion v {ω | ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime Kᶜ ω} ≤
        ENNReal.ofReal b := IsGoodAnnulus.avoid_compact_le hg hK hKm hv
  have havoid : planarBrownianMotion x {ω | ContinuousPath.exitTime A ω ≤
      ContinuousPath.exitTime Kᶜ ω} ≤ ENNReal.ofReal b + 2 * ε := by
    by_cases hxs : x ∈ sphere w (4*r)
    · exact (hbound x hxs).trans (le_add_right le_rfl)
    · have hE := measurableSet_avoid_before_exit hA hK
      have hcomp := planarBrownian_avoidance_le_of_circle_hitting hA hAb hE
        (show x ∈ A \ sphere w (4*r) from ⟨hx, hxs⟩) (ENNReal.ofReal b) hbound
      apply hcomp.trans
      gcongr
      exact (hnear w x y hy hxy).le
  apply (measure_mono ?_).trans havoid
  intro ω hω
  exact hω.trans (ContinuousPath.exitTime_mono hXK ω)

end HarmonicBalls.Section6

import HarmonicBalls.Proofs.Sec6.UniformTranslatedCircleCrossing
import HarmonicBalls.Proofs.Sec6.ScaledAnnularReturn

/-! # Scale-uniform circle crossing

A Brownian motion started close to the middle circle hits it before exiting
an annulus, uniformly over positive scales and centres.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology Pointwise

/-- The start-point modulus is proportional to the annulus radius and is
independent of the centre and scale. -/
theorem exists_scale_uniform_exit_before_circle
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → ∀ w x y : ℂ,
      y ∈ sphere w (4*r) → dist x y < η*r →
      planarBrownianMotion x {ω | ContinuousPath.exitTime (annulus w (3*r) (5*r)) ω ≤
        ContinuousPath.exitTime (annulus w (3*r) (5*r) \ sphere w (4*r)) ω} < ε := by
  obtain ⟨η, hη, hunit⟩ := uniform_planarBrownian_exit_before_translated_circle
    (r := 1) (by norm_num) hε
  refine ⟨η, hη, ?_⟩
  intro r hr w x y hy hxy
  let k : ℝ := r⁻¹
  have hk : 0 < k := inv_pos.mpr hr
  let f : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  let c : ℝ≥0 := ⟨r^2, sq_nonneg r⟩
  have hc : 0 < c := by change (0 : ℝ) < r^2; positivity
  have hscale : (Real.sqrt c)⁻¹ = k := by
    change (Real.sqrt (r^2))⁻¹ = r⁻¹
    rw [Real.sqrt_sq hr.le]
  have hmap := planarBrownianMotion_map_spacetime_smul x hk hc hscale
  let A := annulus w (3*r) (5*r)
  let S := sphere w (4*r)
  have hA : f '' A = annulus (k • w) (3*1) (5*1) := by
    change (fun u : ℂ => k • u) '' annulus w (3*r) (5*r) = _
    rw [image_smul_annulus hk]
    have h3 : k * (3*r) = 3*1 := by dsimp [k]; field_simp
    have h5 : k * (5*r) = 5*1 := by dsimp [k]; field_simp
    rw [h3, h5]
  have hS : f '' S = sphere (k • w) (4*1) := by
    change (fun u : ℂ => k • u) '' sphere w (4*r) = _
    change k • sphere w (4*r) = _
    rw [_root_.smul_sphere' hk.ne', Real.norm_eq_abs, abs_of_pos hk]
    congr 1
    dsimp [k]
    field_simp
  have heq := measure_exitTime_order_eq_of_spacetime_homeomorph f A (A \ S) c hc
    (planarBrownianMotion x) (planarBrownianMotion (k • x)) hmap
  rw [image_sdiff f.injective, hA, hS] at heq
  rw [← heq]
  apply hunit (k • w) (k • x) (k • y)
  · have hy' : f y ∈ f '' S := mem_image_of_mem f hy
    rw [hS] at hy'
    change k • y ∈ sphere (k • w) (4*1) at hy'
    exact hy'
  · rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hk]
    dsimp [k]
    exact (mul_lt_mul_of_pos_left hxy hk).trans_eq (by dsimp [k]; field_simp)

/-- The starting-point avoidance estimate has a modulus proportional to the radius and independent of the
scale, centre, measure, good-annulus witness and thresholds. -/
theorem scale_uniform_goodAnnulus_avoidance_near_circle
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → ∀ (μ : Measure ℂ) (w : ℂ) (a b : ℝ),
      μ (annulus w (3*r) (5*r)) ≠ ∞ → IsGoodAnnulus μ r w a b →
      ∀ x y : ℂ, y ∈ sphere w (4*r) → dist x y < δ*r →
      x ∈ annulus w (3*r) (5*r) → ∀ X : Set ℂ, MeasurableSet X →
      X ⊆ annulus w (3*r) (5*r) →
      μ X < ENNReal.ofReal a * μ (annulus w (3*r) (5*r)) →
      planarBrownianMotion x {ω | ContinuousPath.exitTime (annulus w (3*r) (5*r)) ω ≤
        ContinuousPath.exitTime X ω} ≤ ENNReal.ofReal b + 2 * ε := by
  obtain ⟨δ, hδ, hnear⟩ := exists_scale_uniform_exit_before_circle hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr μ w a b hfin hg x y hy hxy hx X hX hXA hm
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
      exact (hnear r hr w x y hy hxy).le
  apply (measure_mono ?_).trans havoid
  intro ω hω
  exact hω.trans (ContinuousPath.exitTime_mono hXK ω)


end HarmonicBalls.Section6

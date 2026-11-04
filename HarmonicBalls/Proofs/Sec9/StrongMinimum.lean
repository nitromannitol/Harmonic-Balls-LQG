import HarmonicBalls.Proofs.Sec9.PotentialMinimum

/-! # Local strong minimum principle -/

namespace HarmonicBalls

open Complex Metric Real Filter Topology Set MeasureTheory InnerProductSpace

/-- A continuous function which is nonnegative on a circle and positive at one point has a
strictly positive circle average. -/
theorem circleAverage_pos_of_nonneg_of_pos {u : ℂ → ℝ} {x y : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : ContinuousOn u (sphere x r))
    (hnonneg : ∀ z ∈ sphere x r, 0 ≤ u z) (hy : y ∈ sphere x r) (hpos : 0 < u y) :
    0 < Real.circleAverage u x r := by
  have hy' : y ∈ circleMap x r '' Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc, abs_of_pos hr]
    exact hy
  obtain ⟨θ, hθ, hθy⟩ := hy'
  have hcont : ContinuousOn (fun θ => u (circleMap x r θ)) (Icc 0 (2 * Real.pi)) :=
    hc.comp (continuous_circleMap x r).continuousOn (fun θ _ => circleMap_mem_sphere x hr.le θ)
  have hint : ∫ _ in (0 : ℝ)..2 * Real.pi, (0 : ℝ) <
      ∫ θ in (0 : ℝ)..2 * Real.pi, u (circleMap x r θ) :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt Real.two_pi_pos
      continuousOn_const hcont (fun θ _ => hnonneg _ (circleMap_mem_sphere x hr.le θ))
      ⟨θ, ⟨hθ.1.le, hθ.2⟩, by simpa [hθy] using hpos⟩
  simp only [intervalIntegral.integral_zero] at hint
  rw [Real.circleAverage_def, smul_eq_mul]
  exact mul_pos (inv_pos.2 Real.two_pi_pos) hint

/-- A nonnegative continuous superharmonic function which vanishes at an interior point
vanishes in an open neighbourhood of that point. -/
theorem IsSuperharmonicOn.exists_ball_eq_zero {U : Set ℂ} {u : ℂ → ℝ}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hs : IsSuperharmonicOn U u)
    (hnonneg : ∀ x ∈ U, 0 ≤ u x) {x : ℂ} (hx : x ∈ U) (hx0 : u x = 0) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧ EqOn u 0 (ball x r) := by
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨r, hr, hrsub, ?_⟩
  intro y hy
  change u y = 0
  by_cases hyx : y = x
  · simpa [hyx] using hx0
  · have hdist : 0 < dist y x := dist_pos.mpr hyx
    have hdistlt : dist y x < r := hy
    have hball : closedBall x (dist y x) ⊆ U := (closedBall_subset_ball hdistlt).trans hrsub
    have hsph : sphere x (dist y x) ⊆ U := sphere_subset_closedBall.trans hball
    have hyS : y ∈ sphere x (dist y x) := mem_sphere.mpr rfl
    have hmean := (hs.2 x hx (dist y x) hdist hball).2
    have hnonnegY := hnonneg y (hrsub hy)
    by_contra hne
    have hpos : 0 < u y := lt_of_le_of_ne hnonnegY (Ne.symm hne)
    have havg := circleAverage_pos_of_nonneg_of_pos hdist (hc.mono hsph)
      (fun z hz => hnonneg z (hsph hz)) hyS hpos
    rw [hx0] at hmean
    linarith

/-- The deterministic boundary comparison in Lemma 9.3, under volume growth and full support. -/
theorem IsHarmonicBallGen.frontier_subset_closure_of_volumeGrowth
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] (hμ : IsLocallyFiniteMeasure μ)
    {A B : Set ℂ} {z : ℂ} (hA : IsHarmonicBallGen μ A z) (hB : IsSubharmonicBall μ B z)
    {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hAcl : closure A ⊆ ball 0 R) (hBcl : closure B ⊆ ball 0 R)
    (hmass : μ.real A = μ.real B) : frontier A ⊆ closure B := by
  intro x hx
  by_contra hxB
  let U : Set ℂ := ball 0 R \ closure B
  let u : ℂ → ℝ := fun x => (∫ y in A, greenFunction (ball 0 R) x y ∂μ) -
    ∫ y in B, greenFunction (ball 0 R) x y ∂μ
  have hAsub : A ⊆ ball (0 : ℂ) R := subset_closure.trans hAcl
  have hBsub : B ⊆ ball (0 : ℂ) R := subset_closure.trans hBcl
  have hUopen : IsOpen U := isOpen_ball.sdiff isClosed_closure
  have hUsub : U ⊆ ball (0 : ℂ) R := sdiff_subset
  have hUB : Disjoint U B := Set.disjoint_left.2 (fun _ hU hB => hU.2 (subset_closure hB))
  have hxU : x ∈ U := ⟨hAcl (frontier_subset_closure hx), hxB⟩
  have hx0 : u x = 0 := hA.greenPotential_sub_eq_zero_on_frontier hB hAcl hBcl hmass ⟨hx, hxB⟩
  obtain ⟨hc, hΔ⟩ := auxiliary_greenPotential_regular hμ hR hV hAsub hBsub
  have hsup : IsSuperharmonicOn U u :=
    auxiliary_greenPotential_superharmonicOn_of_disjoint hμ hR hV hAsub hBsub hUopen hUsub hUB
  have hnonneg : ∀ y ∈ U, 0 ≤ u y := fun y hy =>
    hA.auxiliary_greenPotential_nonneg hμ hB hR hV hAcl hBcl hmass
      (ball_subset_closedBall (hUsub hy))
  obtain ⟨r, hr, hrsub, hzero⟩ := hsup.exists_ball_eq_zero hUopen
    (hc.mono (hUsub.trans ball_subset_closedBall)) hnonneg hxU hx0
  have hrB : Disjoint (ball x r) B := hUB.mono_left hrsub
  exact not_eqOn_zero_of_hasLaplacian_boundary hA.1.1 isOpen_ball
    (hrsub.trans hUsub) hrB hΔ hx (mem_ball_self hr) hzero

end HarmonicBalls

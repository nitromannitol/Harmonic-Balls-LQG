import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-! # Capped Green barriers for a point

The Green function of a disc, multiplied by a positive constant and capped at
`M`, gives a continuous superharmonic barrier which equals `M` near its pole.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology InnerProductSpace

/-- The Green barrier capped at `M`, with its continuous value at the pole. -/
noncomputable def cappedGreenBarrier (R : ℝ) (a : ℂ) (c M : ℝ) (x : ℂ) : ℝ :=
  if x = a then M else min (c * greenFunction (ball (0 : ℂ) R) a x) M

/-- The capped Green barrier is constant on a neighbourhood of its pole. -/
theorem cappedGreenBarrier_eventually_eq {R c M : ℝ} {a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hc : 0 < c) :
    cappedGreenBarrier R a c M =ᶠ[𝓝 a] fun _ => M := by
  have hbig : ∀ᶠ x in 𝓝[≠] a, M ≤ c * greenFunction (ball (0 : ℂ) R) a x :=
    (Tendsto.const_mul_atTop hc (tendsto_greenFunction_ball_pole ha)).eventually (eventually_ge_atTop M)
  rw [eventually_nhdsWithin_iff] at hbig
  filter_upwards [hbig] with x hx
  by_cases hxa : x = a
  · simp [cappedGreenBarrier, hxa]
  · simp [cappedGreenBarrier, hxa, min_eq_right (hx hxa)]

/-- The capped Green barrier is continuous on the closed disc. -/
theorem continuousOn_cappedGreenBarrier {R c M : ℝ} {a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hc : 0 < c) :
    ContinuousOn (cappedGreenBarrier R a c M) (closedBall (0 : ℂ) R) := by
  intro x hx
  by_cases hxa : x = a
  · subst x
    exact (continuousAt_const.congr (cappedGreenBarrier_eventually_eq ha hc).symm).continuousWithinAt
  · have hG : ContinuousAt (greenFunction (ball (0 : ℂ) R) a) x :=
      (continuousOn_greenFunction_ball ha).continuousAt (isOpen_compl_singleton.mem_nhds hxa)
    have hs : ContinuousWithinAt (fun y => min (c * greenFunction (ball (0 : ℂ) R) a y) M)
        (closedBall (0 : ℂ) R) x :=
      (continuousWithinAt_const.mul hG.continuousWithinAt).min continuousWithinAt_const
    refine hs.congr_of_eventuallyEq ?_ (by simp [cappedGreenBarrier, hxa])
    filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hxa)] with y hy
    have hya : y ≠ a := by simpa using hy
    simp [cappedGreenBarrier, hya]

/-- The capped Green barrier is superharmonic in the disc, equivalently its
weak Laplacian is nonpositive. -/
theorem laplacianLE_cappedGreenBarrier {R c M : ℝ} {a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hc : 0 < c) :
    LaplacianLE (cappedGreenBarrier R a c M) 0 (ball (0 : ℂ) R) := by
  let w := cappedGreenBarrier R a c M
  let G := greenFunction (ball (0 : ℂ) R) a
  have hwc : ContinuousOn w (closedBall (0 : ℂ) R) := continuousOn_cappedGreenBarrier ha hc
  have hwa : w a = M := by simp [w, cappedGreenBarrier]
  have hwne : ∀ x, x ≠ a → w x = min (c * G x) M := fun x hx => by
    simp [w, G, cappedGreenBarrier, hx]
  have hwev : w =ᶠ[𝓝 a] fun _ => M := cappedGreenBarrier_eventually_eq ha hc
  have hwle : ∀ x, w x ≤ M := by
    intro x
    by_cases hx : x = a
    · simp [hx, hwa]
    · rw [hwne x hx]
      exact min_le_right _ _
  have hwci : ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x r ⊆ ball 0 R → CircleIntegrable w x r :=
    fun hr hsub => (hwc.mono ((sphere_subset_closedBall.trans hsub).trans ball_subset_closedBall)).circleIntegrable
      hr.le
  have hloc : ∀ x ∈ ball (0 : ℂ) R, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable w x r ∧ Real.circleAverage w x r ≤ w x := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      obtain ⟨ε, hε, hεw⟩ := Metric.eventually_nhds_iff.mp hwev
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_ball a hx
      refine ⟨min ε ρ, lt_min hε hρ, fun r hr => ?_⟩
      have hrsub : closedBall a r ⊆ ball 0 R :=
        (closedBall_subset_ball (lt_of_lt_of_le hr.2 (min_le_right _ _))).trans hρsub
      refine ⟨hwci hr.1 hrsub, ?_⟩
      have hsph : EqOn w (fun _ => M) (sphere a |r|) := fun y hy => by
        rw [abs_of_pos hr.1] at hy
        exact hεw (lt_of_le_of_lt (le_of_eq (mem_sphere.mp hy))
          (lt_of_lt_of_le hr.2 (min_le_left _ _)))
      rw [Real.circleAverage_congr_sphere hsph, Real.circleAverage_const, hwa]
    · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.sdiff isClosed_singleton) x ⟨hx, hxa⟩
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      have hsuba : closedBall x r ⊆ ball 0 R \ {a} := (closedBall_subset_ball hr.2).trans hρsub
      have hrsub : closedBall x r ⊆ ball 0 R := fun y hy => (hsuba hy).1
      have hwi := hwci hr.1 hrsub
      have hGc : ContinuousOn G (sphere x r) :=
        (continuousOn_greenFunction_ball ha).mono fun y hy => (hsuba (sphere_subset_closedBall hy)).2
      have hcGi : CircleIntegrable (fun y => c * G y) x r :=
        (continuousOn_const.mul hGc).circleIntegrable hr.1.le
      have hGeq : Real.circleAverage G x r = G x :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq
          ((harmonicOnNhd_greenFunction_ball ha).mono (by rw [abs_of_pos hr.1]; exact hsuba))
      have hcG : Real.circleAverage (fun y => c * G y) x r = c * Real.circleAverage G x r := by
        have := Real.circleAverage_fun_smul (f := G) (c := x) (R := r) (a := c)
        simpa [smul_eq_mul] using this
      have hne : ∀ y ∈ sphere x |r|, y ≠ a := fun y hy => by
        rw [abs_of_pos hr.1] at hy
        exact (hsuba (sphere_subset_closedBall hy)).2
      have h1 : Real.circleAverage w x r ≤ Real.circleAverage (fun y => c * G y) x r :=
        Real.circleAverage_mono hwi hcGi fun y hy => by
          rw [hwne y (hne y hy)]
          exact min_le_left _ _
      have h2 : Real.circleAverage w x r ≤ M := by
        have := Real.circleAverage_mono hwi (continuousOn_const.circleIntegrable' (f := fun _ : ℂ => M))
          fun y _ => hwle y
        rwa [Real.circleAverage_const] at this
      rw [hcG, hGeq] at h1
      refine ⟨hwi, ?_⟩
      rw [hwne x hxa]
      exact le_min h1 h2
  have hlsc : LowerSemicontinuousOn w (ball 0 R) := (hwc.mono ball_subset_closedBall).lowerSemicontinuousOn
  have hwsh : IsSuperharmonicOn (ball 0 R) w := ⟨hlsc, fun x hx r hr hsub =>
    ⟨hwci hr hsub, circleAverage_le_of_localSuperMean hlsc hloc hr hsub (hwci hr hsub)⟩⟩
  exact laplacianLEOfSuperharmonicStep_holds _ w isOpen_ball (hwc.mono ball_subset_closedBall) hwsh

/-- A capped Green barrier with nonnegative cap is nonnegative. -/
theorem cappedGreenBarrier_nonneg {R c M : ℝ} {a x : ℂ}
    (hc : 0 ≤ c) (hM : 0 ≤ M) : 0 ≤ cappedGreenBarrier R a c M x := by
  by_cases hxa : x = a
  · simp [cappedGreenBarrier, hxa, hM]
  · simp only [cappedGreenBarrier, hxa, ↓reduceIte]
    exact le_min (mul_nonneg hc (greenFunction_nonneg isBounded_ball a x)) hM

/-- Away from the pole, the capped Green barrier tends to zero as its
coefficient tends to zero from above. -/
theorem tendsto_cappedGreenBarrier_coefficient_zero {R M : ℝ} {a x : ℂ}
    (hxa : x ≠ a) (hM : 0 ≤ M) :
    Tendsto (fun c : ℝ => cappedGreenBarrier R a c M x) (𝓝[>] 0) (𝓝 0) := by
  have hcont : ContinuousAt (fun c : ℝ => min (c * greenFunction (ball (0 : ℂ) R) a x) M) 0 := by
    fun_prop
  simpa [cappedGreenBarrier, hxa, min_eq_left hM] using
    hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

#print axioms cappedGreenBarrier_nonneg
#print axioms tendsto_cappedGreenBarrier_coefficient_zero

#print axioms cappedGreenBarrier_eventually_eq
#print axioms continuousOn_cappedGreenBarrier
#print axioms laplacianLE_cappedGreenBarrier

end HarmonicBalls

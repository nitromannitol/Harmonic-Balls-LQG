import HarmonicBalls.Proofs.Sec5.PuncturedSubharmonicMaximum

/-! # Maximum principle with finitely many punctures -/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

/-- A finite sum of logarithmic point barriers is harmonic off their poles. -/
theorem harmonicOnNhd_finset_log_barrier (K : Finset ℂ) (ε : ℝ) :
    HarmonicOnNhd (fun x : ℂ => ∑ a ∈ K, ε * Real.log ‖x - a‖)
      ((K : Set ℂ)ᶜ) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    simp
  | @insert a K ha ih =>
    intro x hx
    have hx' : x ≠ a ∧ x ∉ K := by simpa using hx
    have hxa : x ≠ a := hx'.1
    have hxK : x ∈ (K : Set ℂ)ᶜ := hx'.2
    have han : AnalyticAt ℂ (fun y : ℂ => y - a) x := by fun_prop
    have hlog := (han.harmonicAt_log_norm (sub_ne_zero.mpr hxa)).const_smul (c := ε)
    convert hlog.add (ih x hxK) using 1
    funext y
    simp [Finset.sum_insert ha, smul_eq_mul]

/-- A subharmonic function on a finitely punctured disc which tends to negative
infinity at each puncture is bounded above by its outer boundary values. -/
theorem isSubharmonicOn_finset_punctured_ball_le_of_tendsto_atBot
    {c : ℂ} {r : ℝ} {f : ℂ → ℝ} {C : ℝ} (K : Finset ℂ)
    (hcont : ContinuousOn f (closedBall c r \ (K : Set ℂ)))
    (hsub : IsSubharmonicOn (ball c r \ (K : Set ℂ)) f)
    (hlim : ∀ a ∈ K, Tendsto f (𝓝[ball c r \ (K : Set ℂ)] a) atBot)
    (hbd : ∀ x ∈ sphere c r, x ∉ K → f x ≤ C) :
    ∀ x ∈ ball c r \ (K : Set ℂ), f x ≤ C := by
  let D := ball c r \ (K : Set ℂ)
  let W := D ∩ f ⁻¹' Ioi C
  have hDo : IsOpen D := isOpen_ball.sdiff K.finite_toSet.isClosed
  have hDW : D ⊆ closedBall c r \ (K : Set ℂ) :=
    fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩
  have hWo : IsOpen W := (hcont.mono hDW).isOpen_inter_preimage hDo isOpen_Ioi
  have hnot : ∀ a ∈ K, a ∉ closure W := by
    intro a ha
    have hnear : ∀ᶠ x in 𝓝[D] a, f x < C :=
      (hlim a ha).eventually (eventually_lt_atBot C)
    have hnotW : ∀ᶠ x in 𝓝 a, x ∉ W := by
      filter_upwards [eventually_nhdsWithin_iff.mp hnear] with x hx hxW
      exact (not_lt_of_ge (le_of_lt hxW.2)) (hx hxW.1)
    rw [mem_closure_iff_frequently, not_frequently]
    exact hnotW
  have hcl : closure W ⊆ closedBall c r \ (K : Set ℂ) := by
    intro x hx
    refine ⟨closure_minimal (inter_subset_left.trans (fun _ hy => ball_subset_closedBall hy.1))
      isClosed_closedBall hx, ?_⟩
    intro hxK
    exact hnot x hxK hx
  have hWe : W = ∅ := by
    refine eq_empty_of_pos_of_subMean (isBounded_ball.subset (inter_subset_left.trans sdiff_subset))
      ((hcont.mono hcl).sub continuousOn_const) (fun x hx => sub_pos.mpr hx.2)
      (fun x hx => ?_) (fun x hx => ?_)
    · have hxc := hcl (frontier_subset_closure hx)
      by_cases hxb : x ∈ ball c r
      · have hxW : x ∉ W := by
          rw [hWo.frontier_eq] at hx
          exact hx.2
        have : f x ≤ C := le_of_not_gt (fun h => hxW ⟨⟨hxb, hxc.2⟩, h⟩)
        exact sub_nonpos.mpr this
      · have hxs : x ∈ sphere c r := by
          rw [mem_sphere]
          exact le_antisymm (mem_closedBall.mp hxc.1) (le_of_not_gt (fun h => hxb (mem_ball.mpr h)))
        exact sub_nonpos.mpr (hbd x hxs hxc.2)
    · obtain ⟨s, hs, hsW⟩ := Metric.isOpen_iff.mp hWo x hx
      have hball : closedBall x (s / 2) ⊆ W :=
        (closedBall_subset_ball (half_lt_self hs)).trans hsW
      refine ⟨s / 2, half_pos hs, hball, ?_⟩
      have hmean := (hsub.2 x hx.1 (s / 2) (half_pos hs)
        (hball.trans inter_subset_left)).2
      rw [circleAverage_neg_fun, Pi.neg_apply] at hmean
      have hfi : CircleIntegrable f x (s / 2) :=
        (hcont.mono (sphere_subset_closedBall.trans (hball.trans (subset_closure.trans hcl)))).circleIntegrable
          (half_pos hs).le
      rw [Real.circleAverage_sub hfi (circleIntegrable_const _ _ _), Real.circleAverage_const]
      simp only [Pi.sub_apply]
      linarith
  intro x hx
  by_contra h
  have : x ∈ W := ⟨hx, not_le.mp h⟩
  simp [hWe] at this

/-- The finite-puncture maximum principle for harmonic functions. -/
theorem harmonicOnNhd_finset_punctured_ball_le_of_tendsto_atBot
    {c : ℂ} {r : ℝ} {f : ℂ → ℝ} {C : ℝ} (K : Finset ℂ)
    (hcont : ContinuousOn f (closedBall c r \ (K : Set ℂ)))
    (hharm : HarmonicOnNhd f (ball c r \ (K : Set ℂ)))
    (hlim : ∀ a ∈ K, Tendsto f (𝓝[ball c r \ (K : Set ℂ)] a) atBot)
    (hbd : ∀ x ∈ sphere c r, x ∉ K → f x ≤ C) :
    ∀ x ∈ ball c r \ (K : Set ℂ), f x ≤ C := by
  have hsub : IsSubharmonicOn (ball c r \ (K : Set ℂ)) f := by
    refine ⟨hharm.continuousOn.neg.lowerSemicontinuousOn, fun x hx s hs hball => ?_⟩
    have hi : CircleIntegrable f x s :=
      (hharm.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hs.le
    have hmean := (hharm.mono (show closedBall x |s| ⊆ ball c r \ (K : Set ℂ) by
      rw [abs_of_pos hs]; exact hball)).circleAverage_eq
    refine ⟨hi.neg, ?_⟩
    rw [circleAverage_neg_fun, Pi.neg_apply, hmean]
  exact isSubharmonicOn_finset_punctured_ball_le_of_tendsto_atBot K hcont hsub hlim hbd

#print axioms isSubharmonicOn_finset_punctured_ball_le_of_tendsto_atBot
#print axioms harmonicOnNhd_finset_punctured_ball_le_of_tendsto_atBot
#print axioms harmonicOnNhd_finset_log_barrier

end HarmonicBalls

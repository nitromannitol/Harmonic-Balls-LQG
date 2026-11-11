import HarmonicBalls.Proofs.Sec5.PuncturedMaximumPrinciple

/-! # Subharmonic maximum principle on a punctured disc

A continuous subharmonic function tending to negative infinity at the removed
point obeys the maximum principle on the punctured disc.
-/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

/-- The maximum principle for a subharmonic function on a punctured disc. -/
theorem isSubharmonicOn_punctured_ball_le_of_tendsto_atBot
    {c a : ℂ} {r : ℝ} {f : ℂ → ℝ} {C : ℝ}
    (hcont : ContinuousOn f (closedBall c r \ {a}))
    (hsub : IsSubharmonicOn (ball c r \ {a}) f)
    (hlim : Tendsto f (𝓝[ball c r \ {a}] a) atBot)
    (hbd : ∀ x ∈ sphere c r, x ≠ a → f x ≤ C) :
    ∀ x ∈ ball c r \ {a}, f x ≤ C := by
  let D := ball c r \ {a}
  let W := D ∩ f ⁻¹' Ioi C
  have hDo : IsOpen D := isOpen_ball.sdiff isClosed_singleton
  have hDW : D ⊆ closedBall c r \ {a} := fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩
  have hWo : IsOpen W := (hcont.mono hDW).isOpen_inter_preimage hDo isOpen_Ioi
  have hnear : ∀ᶠ x in 𝓝[D] a, f x < C := hlim.eventually (eventually_lt_atBot C)
  have hnot : ∀ᶠ x in 𝓝 a, x ∉ W := by
    filter_upwards [eventually_nhdsWithin_iff.mp hnear] with x hx hxW
    exact (not_lt_of_ge (le_of_lt hxW.2)) (hx hxW.1)
  have haW : a ∉ closure W := by
    rw [mem_closure_iff_frequently, not_frequently]
    exact hnot
  have hcl : closure W ⊆ closedBall c r \ {a} := by
    intro x hx
    refine ⟨closure_minimal (inter_subset_left.trans (fun _ hy => ball_subset_closedBall hy.1))
      isClosed_closedBall hx, ?_⟩
    simpa only [mem_singleton_iff] using fun h : x = a => haW (h ▸ hx)
  have hWe : W = ∅ := by
    refine eq_empty_of_pos_of_subMean (isBounded_ball.subset (inter_subset_left.trans sdiff_subset))
      ((hcont.mono hcl).sub continuousOn_const) (fun x hx => sub_pos.mpr hx.2)
      (fun x hx => ?_) (fun x hx => ?_)
    · have hxc := hcl (frontier_subset_closure hx)
      have hxa : x ≠ a := by simpa using hxc.2
      by_cases hxb : x ∈ ball c r
      · have hxW : x ∉ W := by
          rw [hWo.frontier_eq] at hx
          exact hx.2
        have : f x ≤ C := le_of_not_gt (fun h => hxW ⟨⟨hxb, hxc.2⟩, h⟩)
        exact sub_nonpos.mpr this
      · have hxs : x ∈ sphere c r := by
          rw [mem_sphere]
          exact le_antisymm (mem_closedBall.mp hxc.1) (le_of_not_gt (fun h => hxb (mem_ball.mpr h)))
        exact sub_nonpos.mpr (hbd x hxs hxa)
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

/-- Adding a harmonic function preserves subharmonicity for continuous functions. -/
theorem IsSubharmonicOn.add_harmonicOnNhd {U : Set ℂ} {f h : ℂ → ℝ}
    (hfc : ContinuousOn f U) (hf : IsSubharmonicOn U f)
    (hh : HarmonicOnNhd h U) : IsSubharmonicOn U (f + h) := by
  have hhc : ContinuousOn h U := hh.continuousOn
  refine ⟨(hfc.add hhc).neg.lowerSemicontinuousOn, fun x hx r hr hball => ?_⟩
  have hfi : CircleIntegrable f x r :=
    (hfc.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le
  have hhi : CircleIntegrable h x r :=
    (hhc.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le
  have havg := (hf.2 x hx r hr hball).2
  rw [circleAverage_neg_fun, Pi.neg_apply] at havg
  have hmean := (hh.mono (show closedBall x |r| ⊆ U by
    rw [abs_of_pos hr]; exact hball)).circleAverage_eq
  refine ⟨(hfi.add hhi).neg, ?_⟩
  rw [circleAverage_neg_fun, Real.circleAverage_add hfi hhi, hmean]
  simp only [Pi.neg_apply, Pi.add_apply]
  linarith

/-- A bounded continuous subharmonic function on a punctured disc obeys the
maximum principle across its interior puncture. -/
theorem isSubharmonicOn_punctured_ball_le_of_continuousOn
    {c a : ℂ} {r C : ℝ} {f : ℂ → ℝ}
    (ha : a ∈ ball c r) (hcont : ContinuousOn f (closedBall c r))
    (hsub : IsSubharmonicOn (ball c r \ {a}) f)
    (hbd : ∀ x ∈ sphere c r, f x ≤ C) :
    ∀ x ∈ closedBall c r, f x ≤ C := by
  have hr : 0 < r := pos_of_mem_ball ha
  have hne : ∀ x ∈ sphere c r, x ≠ a := by
    intro x hx hxa
    subst x
    have h1 := mem_ball.mp ha
    have h2 := mem_sphere.mp hx
    linarith
  have hlogc : ContinuousOn (fun x : ℂ => Real.log ‖x - a‖) (sphere c r) := by
    intro x hx
    have han : AnalyticAt ℂ (fun y : ℂ => y - a) x := by fun_prop
    exact (han.harmonicAt_log_norm (sub_ne_zero.mpr (hne x hx))).1.continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn hlogc
  have hlogbd : ∀ x ∈ sphere c r, Real.log ‖x - a‖ ≤ B := by
    intro x hx
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB x hx)
  have hfca : ContinuousAt f a :=
    (hcont a (ball_subset_closedBall ha)).continuousAt
      (mem_of_superset (isOpen_ball.mem_nhds ha) ball_subset_closedBall)
  intro x hx
  by_cases hxb : x ∈ sphere c r
  · exact hbd x hxb
  have hxball : x ∈ ball c r := by
    have h1 := mem_closedBall.mp hx
    have h2 : dist x c ≠ r := fun h => hxb (mem_sphere.mpr h)
    exact mem_ball.mpr (lt_of_le_of_ne h1 h2)
  have hpunct : ∀ y ∈ ball c r \ {a}, f y ≤ C := by
    intro y hy
    by_contra hn
    have hpos : 0 < f y - C := sub_pos.mpr (not_le.mp hn)
    let ε : ℝ := (f y - C) / (|B| + |Real.log ‖y - a‖| + 1)
    have hden : 0 < |B| + |Real.log ‖y - a‖| + 1 := by positivity
    have hε : 0 < ε := div_pos hpos hden
    let g : ℂ → ℝ := fun z => ε * Real.log ‖z - a‖
    have hharm : HarmonicOnNhd g (ball c r \ {a}) := by
      intro z hz
      have han : AnalyticAt ℂ (fun w : ℂ => w - a) z := by fun_prop
      have hza : z ≠ a := by simpa using hz.2
      exact (han.harmonicAt_log_norm (sub_ne_zero.mpr hza)).const_smul (c := ε)
    have hgc : ContinuousOn g (closedBall c r \ {a}) := by
      intro z hz
      have han : AnalyticAt ℂ (fun w : ℂ => w - a) z := by fun_prop
      have hza : z ≠ a := by simpa using hz.2
      exact ((han.harmonicAt_log_norm (sub_ne_zero.mpr hza)).const_smul (c := ε)).1.continuousAt.continuousWithinAt
    have hf : ContinuousOn f (ball c r \ {a}) := hcont.mono (sdiff_subset.trans ball_subset_closedBall)
    have hs := hsub.add_harmonicOnNhd hf hharm
    have hlog : Tendsto (fun z : ℂ => Real.log ‖z - a‖) (𝓝[ball c r \ {a}] a) atBot :=
      (Real.tendsto_log_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE a)).mono_left
        (nhdsWithin_mono a (fun _ hz => hz.2))
    have ht : Tendsto (f + g) (𝓝[ball c r \ {a}] a) atBot := by
      have hf' := hfca.tendsto.mono_left (nhdsWithin_le_nhds (s := ball c r \ {a}))
      change Tendsto (fun z => f z + ε * Real.log ‖z - a‖) _ _
      simpa [add_comm] using (hlog.const_mul_atBot hε).atBot_add hf'
    have hcomp := isSubharmonicOn_punctured_ball_le_of_tendsto_atBot
      ((hcont.mono sdiff_subset).add hgc) hs ht
      (C := C + ε * B) (by
        intro z hz hza
        simp only [Pi.add_apply, g]
        exact add_le_add (hbd z hz) (mul_le_mul_of_nonneg_left (hlogbd z hz) hε.le)) y hy
    simp only [Pi.add_apply, g] at hcomp
    have hεeq : ε * (|B| + |Real.log ‖y - a‖| + 1) = f y - C := by
      dsimp [ε]; field_simp
    nlinarith [le_abs_self B, neg_abs_le (Real.log ‖y - a‖)]
  by_cases hxa : x = a
  · subst x
    apply le_of_tendsto (hfca.tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ)))
    have hevent : ∀ᶠ y in 𝓝[{a}ᶜ] a, y ∈ ball c r :=
      (show ∀ᶠ y in 𝓝 a, y ∈ ball c r from isOpen_ball.mem_nhds ha).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hevent, self_mem_nhdsWithin] with y hy hya
    exact hpunct y ⟨hy, hya⟩
  · exact hpunct x ⟨hxball, by simpa using hxa⟩

end HarmonicBalls

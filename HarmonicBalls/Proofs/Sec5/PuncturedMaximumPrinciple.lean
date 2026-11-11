import HarmonicBalls.Proofs.Sec5.HarmonicMinorantPuncture
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-! # Maximum principle on a punctured disc

A harmonic function bounded above on the outer circle and tending to negative
infinity at the removed point is bounded above throughout the punctured disc.
-/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

/-- The maximum principle on a disc with one point removed, when the function
has negative infinite limit at the removed point. -/
theorem harmonicOnNhd_punctured_ball_le_of_tendsto_atBot
    {c a : ℂ} {r : ℝ} {f : ℂ → ℝ} {C : ℝ}
    (hcont : ContinuousOn f (closedBall c r \ {a}))
    (hharm : HarmonicOnNhd f (ball c r \ {a}))
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
  have hg : HarmonicOnNhd (f - fun _ => C) D := hharm.sub (harmonicOnNhd_const C)
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
      have hsub : closedBall x (s / 2) ⊆ W :=
        (closedBall_subset_ball (half_lt_self hs)).trans hsW
      refine ⟨s / 2, half_pos hs, hsub, ?_⟩
      have hmean := (hg.mono (show closedBall x |s / 2| ⊆ D by
        rw [abs_of_pos (half_pos hs)]
        exact hsub.trans inter_subset_left)).circleAverage_eq
      exact le_of_eq hmean.symm
  intro x hx
  by_contra h
  have : x ∈ W := ⟨hx, not_le.mp h⟩
  simp [hWe] at this

/-- A logarithmically perturbed harmonic minorant obeys the punctured-disc
maximum principle after subtracting a function harmonic across the puncture. -/
theorem IsHarmonicMinorant.add_log_sub_le_of_boundary
    {O : Set ℂ} {z a c : ℂ} {r ε C : ℝ} {h q : ℂ → ℝ}
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    (haz : a ≠ z) (hε : 0 < ε) (ha : a ∈ closedBall c r)
    (hO : closedBall c r \ {a} ⊆ O) (hq : HarmonicOnNhd q (closedBall c r))
    (hbd : ∀ x ∈ sphere c r, x ≠ a →
      h x + ε * Real.log ‖x - a‖ - q x ≤ C) :
    ∀ x ∈ ball c r \ {a}, h x + ε * Real.log ‖x - a‖ - q x ≤ C := by
  let g : ℂ → ℝ := fun x => h x + ε * Real.log ‖x - a‖ - q x
  have hsub : closedBall c r \ {a} ⊆ O \ {a} := fun _ hx => ⟨hO hx, hx.2⟩
  have hg : HarmonicOnNhd g (closedBall c r \ {a}) :=
    (hh.harmonicOnNhd_add_log_punctured ε).mono hsub |>.sub (hq.mono sdiff_subset)
  have hlim : Tendsto g (𝓝[ball c r \ {a}] a) atBot := by
    have hsub' : ball c r \ {a} ⊆ O \ {a} :=
      fun _ hx => hsub ⟨ball_subset_closedBall hx.1, hx.2⟩
    have ht := (hh.tendsto_add_log_atBot_at_puncture haz hε).mono_left
      (nhdsWithin_mono a hsub')
    have hq' : Tendsto (-q) (𝓝[ball c r \ {a}] a) (𝓝 ((-q) a)) :=
      (hq a ha).1.continuousAt.neg.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [g, sub_eq_add_neg, Pi.neg_apply] using ht.atBot_add hq'
  exact harmonicOnNhd_punctured_ball_le_of_tendsto_atBot hg.continuousOn
    (hg.mono (fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩)) hlim hbd

end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.PuncturedMaximumPrinciple
import HarmonicBalls.Proofs.Sec5.LocallyFinitePunctureGreen

/-! # Maximum principle away from a closed set

A harmonic function with negative infinite limit at every deleted point is
controlled by its values on the outer circle.
-/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

/-- Maximum principle on a disc with a closed set removed. -/
theorem harmonicOnNhd_ball_sdiff_le_of_tendsto_atBot
    {c : ℂ} {K : Set ℂ} {r : ℝ} {f : ℂ → ℝ} {C : ℝ}
    (hK : IsClosed K)
    (hcont : ContinuousOn f (closedBall c r \ K))
    (hharm : HarmonicOnNhd f (ball c r \ K))
    (hlim : ∀ a ∈ K, Tendsto f (𝓝[ball c r \ K] a) atBot)
    (hbd : ∀ x ∈ sphere c r, x ∉ K → f x ≤ C) :
    ∀ x ∈ ball c r \ K, f x ≤ C := by
  let D := ball c r \ K
  let W := D ∩ f ⁻¹' Ioi C
  have hDo : IsOpen D := isOpen_ball.sdiff hK
  have hDW : D ⊆ closedBall c r \ K := fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩
  have hWo : IsOpen W := (hcont.mono hDW).isOpen_inter_preimage hDo isOpen_Ioi
  have haW : ∀ a ∈ K, a ∉ closure W := by
    intro a ha
    have hnear : ∀ᶠ x in 𝓝[D] a, f x < C :=
      (hlim a ha).eventually (eventually_lt_atBot C)
    have hnot : ∀ᶠ x in 𝓝 a, x ∉ W := by
      filter_upwards [eventually_nhdsWithin_iff.mp hnear] with x hx hxW
      exact (not_lt_of_ge (le_of_lt hxW.2)) (hx hxW.1)
    rw [mem_closure_iff_frequently, not_frequently]
    exact hnot
  have hcl : closure W ⊆ closedBall c r \ K := by
    intro x hx
    refine ⟨closure_minimal (inter_subset_left.trans (fun _ hy => ball_subset_closedBall hy.1))
      isClosed_closedBall hx, ?_⟩
    exact fun hxK => haW x hxK hx
  have hg : HarmonicOnNhd (f - fun _ => C) D := hharm.sub (harmonicOnNhd_const C)
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


/-- A harmonic barrier that tends to negative infinity at every deleted point
controls a Newtonian harmonic minorant on a punctured disc. -/
theorem IsHarmonicMinorant.add_barrier_sub_le_of_boundary
    {O K : Set ℂ} {z c : ℂ} {r ε C : ℝ} {h p q : ℂ → ℝ}
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    (hKclosed : IsClosed K) (hKz : ∀ a ∈ K, a ≠ z)
    (hK : K ⊆ closedBall c r) (hε : 0 < ε)
    (hO : closedBall c r \ K ⊆ O)
    (hp : HarmonicOnNhd p (closedBall c r \ K))
    (hlimp : ∀ a ∈ K, Tendsto p (𝓝[ball c r \ K] a) atBot)
    (hq : HarmonicOnNhd q (closedBall c r))
    (hbd : ∀ x ∈ sphere c r, x ∉ K → h x + ε * p x - q x ≤ C) :
    ∀ x ∈ ball c r \ K, h x + ε * p x - q x ≤ C := by
  let g : ℂ → ℝ := fun x => h x + ε * p x - q x
  have hg : HarmonicOnNhd g (closedBall c r \ K) := by
    convert ((hh.1.mono hO).add (hp.const_smul (c := ε))).sub (hq.mono sdiff_subset) using 1
  have hlim : ∀ a ∈ K, Tendsto g (𝓝[ball c r \ K] a) atBot := by
    intro a ha
    obtain ⟨δ, M, hδ, hbound⟩ :=
      exists_uniform_harmonicMinorant_upper_bound_ne_pole (O := O) (hKz a ha)
    have hball : ∀ᶠ x in 𝓝[ball c r \ K] a, x ∈ ball a δ :=
      (show ∀ᶠ x in 𝓝 a, x ∈ ball a δ from
        isOpen_ball.mem_nhds (mem_ball_self hδ)).filter_mono nhdsWithin_le_nhds
    have ht : Tendsto (fun x => M + ε * p x) (𝓝[ball c r \ K] a) atBot := by
      simpa [add_comm] using ((hlimp a ha).const_mul_atBot hε).atBot_add tendsto_const_nhds
    have hq' : Tendsto (-q) (𝓝[ball c r \ K] a) (𝓝 ((-q) a)) :=
      (hq a (hK ha)).1.continuousAt.neg.tendsto.mono_left nhdsWithin_le_nhds
    apply tendsto_atBot_mono' _ _ (ht.atBot_add hq')
    filter_upwards [hball, self_mem_nhdsWithin] with x hx hxD
    have hxO := hO ⟨ball_subset_closedBall hxD.1, hxD.2⟩
    have hb := hbound h hh x ⟨hxO, hx⟩
    dsimp [g]
    linarith
  exact harmonicOnNhd_ball_sdiff_le_of_tendsto_atBot hKclosed hg.continuousOn
    (hg.mono (fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩)) hlim hbd

/-- A bounded-above harmonic barrier removes a closed set for comparison of
Newtonian harmonic minorants with harmonic functions. -/
theorem IsHarmonicMinorant.sub_le_of_boundary_of_barrier
    {O K : Set ℂ} {z c : ℂ} {r C B : ℝ} {h p q : ℂ → ℝ}
    (hh : IsHarmonicMinorant O (newtonKernelEReal z) h)
    (hKclosed : IsClosed K) (hKz : ∀ a ∈ K, a ≠ z)
    (hK : K ⊆ closedBall c r) (hO : closedBall c r \ K ⊆ O)
    (hp : HarmonicOnNhd p (closedBall c r \ K))
    (hlimp : ∀ a ∈ K, Tendsto p (𝓝[ball c r \ K] a) atBot)
    (hpbd : ∀ x ∈ sphere c r, x ∉ K → p x ≤ B)
    (hq : HarmonicOnNhd q (closedBall c r))
    (hbd : ∀ x ∈ sphere c r, x ∉ K → h x - q x ≤ C) :
    ∀ x ∈ ball c r \ K, h x - q x ≤ C := by
  intro x hx
  have hε : ∀ ε > 0, h x - q x ≤ C + ε * (B - p x) := by
    intro ε hεpos
    have hbound := hh.add_barrier_sub_le_of_boundary hKclosed hKz hK hεpos hO hp hlimp hq
      (C := C + ε * B) (fun y hy hyK => by
        have := mul_le_mul_of_nonneg_left (hpbd y hy hyK) hεpos.le
        linarith [hbd y hy hyK]) x hx
    nlinarith
  have hlim : Tendsto (fun ε : ℝ => C + ε * (B - p x)) (𝓝[>] 0) (𝓝 C) := by
    have hc : ContinuousAt (fun ε : ℝ => C + ε * (B - p x)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  exact hε ε hεpos

/-- A harmonic minorant on a disc with closed polar barriers is bounded by
the full-disc greatest harmonic minorant. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_barriers
    {R : ℝ} {z x : ℂ} (K : Set ℂ)
    (hK : IsClosed K)
    (hbarrier : ∀ ρ : ℝ, ρ < R → ∃ (p : ℂ → ℝ) (B : ℝ),
      HarmonicOnNhd p (closedBall 0 ρ \ (K ∩ closedBall 0 ρ)) ∧
      (∀ a ∈ K ∩ closedBall 0 ρ,
        Tendsto p (𝓝[ball 0 ρ \ (K ∩ closedBall 0 ρ)] a) atBot) ∧
      (∀ y ∈ sphere 0 ρ, y ∉ K ∩ closedBall 0 ρ → p y ≤ B))
    (hz : z ∈ ball (0 : ℂ) R \ K)
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) h)
    (hx : x ∈ ball (0 : ℂ) R \ K) :
    h x ≤ greatestHarmonicMinorantBall R z x := by
  classical
  have hzn : ‖z‖ < R := mem_ball_zero_iff.mp hz.1
  have hxn : ‖x‖ < R := mem_ball_zero_iff.mp hx.1
  have hR : 0 < R := (norm_nonneg z).trans_lt hzn
  let m := max ‖z‖ ‖x‖
  have hmR : m < R := max_lt hzn hxn
  have hzm : ‖z‖ ≤ m := le_max_left _ _
  have hxm : ‖x‖ ≤ m := le_max_right _ _
  let B : ℝ → ℝ := fun ρ =>
    (4 * Real.pi)⁻¹ * ((R ^ 2 - ‖z‖ ^ 2) * (R ^ 2 - ρ ^ 2) / (R ^ 2 * (ρ - ‖z‖) ^ 2))
  have hgB : ∀ ρ ∈ Ioo m R, h x - greatestHarmonicMinorantBall R z x ≤ B ρ := by
    rintro ρ ⟨hmρ, hρR⟩
    have hzρ : ‖z‖ < ρ := hzm.trans_lt hmρ
    have hxρ : ‖x‖ < ρ := hxm.trans_lt hmρ
    let J := K ∩ closedBall (0 : ℂ) ρ
    obtain ⟨p, Bp, hp, hlimp, hpbd⟩ := hbarrier ρ hρR
    have hJclosed : IsClosed J := hK.inter isClosed_closedBall
    have hKρ : J ⊆ closedBall (0 : ℂ) ρ := inter_subset_right
    have hKz : ∀ a ∈ J, a ≠ z := by
      intro a ha he
      exact hz.2 (he ▸ ha.1)
    have hq : HarmonicOnNhd (greatestHarmonicMinorantBall R z) (closedBall 0 ρ) :=
      (isHarmonicMinorant_greatestHarmonicMinorantBall hz.1).1.mono
        (closedBall_subset_ball hρR)
    have hO : closedBall (0 : ℂ) ρ \ J ⊆ ball 0 R \ K := by
      intro y hy
      refine ⟨closedBall_subset_ball hρR hy.1, ?_⟩
      intro hyK
      apply hy.2
      exact ⟨hyK, hy.1⟩
    apply hh.sub_le_of_boundary_of_barrier hJclosed hKz hKρ hO hp hlimp hpbd hq
      (C := B ρ) _ x ⟨mem_ball_zero_iff.mpr hxρ, fun hxJ => hx.2 hxJ.1⟩
    intro y hy hyK
    have hyn : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hy
    have hyz : y ≠ z := by rintro rfl; exact hzρ.ne hyn
    have hyR : ‖y‖ < R := hyn ▸ hρR
    have hpos := norm_sub_conj_mul_pos hR hzn hyR.le
    have h1 : h y ≤ newtonKernel z y := by
      have hyK' : y ∉ K := by
        intro hy
        apply hyK
        exact ⟨hy, mem_closedBall_zero_iff.mpr (le_of_eq hyn)⟩
      have h := hh.2 y ⟨mem_ball_zero_iff.mpr hyR, hyK'⟩
      simpa [newtonKernelEReal, hyz] using h
    have h2 := newtonKernel_sub_greenBall hR (Ne.symm hyz) hpos.ne'
    have h3 := greenBall_le_of_norm_eq hR hzρ hyn hρR.le
    dsimp only [B]
    linarith
  have hB : Tendsto B (𝓝[<] R) (𝓝 0) := by
    have hden : R ^ 2 * (R - ‖z‖) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 (sub_ne_zero.2 hzn.ne'))
    have hc : ContinuousAt B R :=
      continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) hden)
    have h0 : B R = 0 := by simp [B]
    rw [← h0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hB (eventually_of_mem (Ioo_mem_nhdsLT hmR) hgB)
  linarith


/-- Closed deletions admitting harmonic barriers on every inner disc preserve
the greatest harmonic minorant at the remaining points. -/
theorem greatestHarmonicMinorant_ball_sdiff_of_barriers {R : ℝ} {z x : ℂ}
    (K : Set ℂ) (hK : IsClosed K)
    (hbarrier : ∀ ρ : ℝ, ρ < R → ∃ (p : ℂ → ℝ) (B : ℝ),
      HarmonicOnNhd p (closedBall 0 ρ \ (K ∩ closedBall 0 ρ)) ∧
      (∀ a ∈ K ∩ closedBall 0 ρ,
        Tendsto p (𝓝[ball 0 ρ \ (K ∩ closedBall 0 ρ)] a) atBot) ∧
      (∀ y ∈ sphere 0 ρ, y ∉ K ∩ closedBall 0 ρ → p y ≤ B))
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) :
    greatestHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) x =
      greatestHarmonicMinorantBall R z x := by
  apply le_antisymm
  · exact iSup₂_le fun _ hh => EReal.coe_le_coe_iff.mpr
      (hh.le_greatestHarmonicMinorantBall_of_barriers K hK hbarrier hz hx)
  · have hq := isHarmonicMinorant_greatestHarmonicMinorantBall hz.1
    have hq' : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z)
        (greatestHarmonicMinorantBall R z) :=
      ⟨fun y hy => hq.1 y hy.1, fun y hy => hq.2 y hy.1⟩
    exact hq'.le_greatestHarmonicMinorant x

/-- The disc Green function is unchanged away from a closed deletion admitting
harmonic barriers on every inner disc. -/
theorem greenFunction_ball_sdiff_of_barriers {R : ℝ} {z x : ℂ}
    (K : Set ℂ) (hK : IsClosed K)
    (hbarrier : ∀ ρ : ℝ, ρ < R → ∃ (p : ℂ → ℝ) (B : ℝ),
      HarmonicOnNhd p (closedBall 0 ρ \ (K ∩ closedBall 0 ρ)) ∧
      (∀ a ∈ K ∩ closedBall 0 ρ,
        Tendsto p (𝓝[ball 0 ρ \ (K ∩ closedBall 0 ρ)] a) atBot) ∧
      (∀ y ∈ sphere 0 ρ, y ∉ K ∩ closedBall 0 ρ → p y ≤ B))
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    greenFunction (ball 0 R \ K) z x = greenFunction (ball 0 R) z x := by
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball_sdiff_of_barriers K hK hbarrier hz hx, EReal.toReal_coe,
    greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball hz.1 hx.1, EReal.toReal_coe]

#print axioms greatestHarmonicMinorant_ball_sdiff_of_barriers
#print axioms greenFunction_ball_sdiff_of_barriers

#print axioms IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_barriers
#print axioms harmonicOnNhd_ball_sdiff_le_of_tendsto_atBot
#print axioms IsHarmonicMinorant.add_barrier_sub_le_of_boundary
#print axioms IsHarmonicMinorant.sub_le_of_boundary_of_barrier

end HarmonicBalls

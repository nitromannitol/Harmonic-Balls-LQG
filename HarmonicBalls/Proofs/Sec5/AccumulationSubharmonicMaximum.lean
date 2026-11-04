import HarmonicBalls.Proofs.Sec5.PuncturedSubharmonicMaximum
import HarmonicBalls.Proofs.Sec5.AccumulationBarrierCover
import HarmonicBalls.Proofs.Sec5.ClosedSetMaximumPrinciple

/-! # Subharmonic comparison away from a closed deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology InnerProductSpace Laplacian

/-- A continuous subharmonic function is bounded by its outer boundary values
when it is strictly below that bound near each point of a closed deletion. -/
theorem isSubharmonicOn_ball_sdiff_le_of_eventually_lt
    {c : ℂ} {K : Set ℂ} {r : ℝ} {f : ℂ → ℝ} {C : ℝ}
    (hK : IsClosed K)
    (hcont : ContinuousOn f (closedBall c r \ K))
    (hsub : IsSubharmonicOn (ball c r \ K) f)
    (hnear : ∀ a ∈ K, ∀ᶠ x in 𝓝[ball c r \ K] a, f x < C)
    (hbd : ∀ x ∈ sphere c r, x ∉ K → f x ≤ C) :
    ∀ x ∈ ball c r \ K, f x ≤ C := by
  let D := ball c r \ K
  let W := D ∩ f ⁻¹' Ioi C
  have hDo : IsOpen D := isOpen_ball.sdiff hK
  have hDW : D ⊆ closedBall c r \ K := fun _ hx => ⟨ball_subset_closedBall hx.1, hx.2⟩
  have hWo : IsOpen W := (hcont.mono hDW).isOpen_inter_preimage hDo isOpen_Ioi
  have haW : ∀ a ∈ K, a ∉ closure W := by
    intro a ha
    have hnot : ∀ᶠ x in 𝓝 a, x ∉ W := by
      filter_upwards [eventually_nhdsWithin_iff.mp (hnear a ha)] with x hx hxW
      exact (not_lt_of_ge (le_of_lt hxW.2)) (hx hxW.1)
    rw [mem_closure_iff_frequently, not_frequently]
    exact hnot
  have hcl : closure W ⊆ closedBall c r \ K := by
    intro x hx
    refine ⟨closure_minimal (inter_subset_left.trans (fun _ hy => ball_subset_closedBall hy.1))
      isClosed_closedBall hx, ?_⟩
    exact fun hxK => haW x hxK hx
  have hWe : W = ∅ := by
    refine eq_empty_of_pos_of_subMean (isBounded_ball.subset (inter_subset_left.trans sdiff_subset))
      ((hcont.mono hcl).sub continuousOn_const) (fun x hx => sub_pos.mpr hx.2)
      (fun x hx => ?_) (fun x hx => ?_)
    · have hxc := hcl (frontier_subset_closure hx)
      by_cases hxb : x ∈ ball c r
      · have hxW : x ∉ W := by
          rw [hWo.frontier_eq] at hx
          exact hx.2
        exact sub_nonpos.mpr (le_of_not_gt (fun h => hxW ⟨⟨hxb, hxc.2⟩, h⟩))
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

/-- Subtracting a continuous superharmonic function from a harmonic function
yields a subharmonic function. -/
theorem HarmonicOnNhd.sub_superharmonic {U : Set ℂ} {h b : ℂ → ℝ}
    (hh : HarmonicOnNhd h U) (hbc : ContinuousOn b U)
    (hb : IsSuperharmonicOn U b) : IsSubharmonicOn U (h - b) := by
  have hsub : IsSubharmonicOn U (-b) := by
    simpa only [IsSubharmonicOn, neg_neg] using hb
  have hsum := hsub.add_harmonicOnNhd hbc.neg hh
  convert hsum using 1
  ext x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
  ring

/-- A nonnegative superharmonic barrier that dominates the local excess near a
closed deletion yields the usual boundary comparison. -/
theorem harmonic_sub_le_of_superharmonic_barrier
    {c : ℂ} {K : Set ℂ} {r C M : ℝ} {h q b : ℂ → ℝ}
    (hK : IsClosed K)
    (hh : HarmonicOnNhd h (closedBall c r \ K))
    (hq : HarmonicOnNhd q (closedBall c r))
    (hbc : ContinuousOn b (closedBall c r))
    (hb : IsSuperharmonicOn (ball c r \ K) b)
    (hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, h y - q y ≤ C + M)
    (hbar : ∀ a ∈ K ∩ closedBall c r, M < b a)
    (hbn : ∀ y ∈ sphere c r, 0 ≤ b y)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y - q y ≤ C) :
    ∀ y ∈ ball c r \ K, h y - q y ≤ C + b y := by
  let D := ball c r \ K
  let f : ℂ → ℝ := fun y => (h y - q y) - b y
  have hdc : D ⊆ closedBall c r \ K :=
    fun _ hy => ⟨ball_subset_closedBall hy.1, hy.2⟩
  have hfc : ContinuousOn f (closedBall c r \ K) :=
    (hh.continuousOn.sub (hq.continuousOn.mono sdiff_subset)).sub (hbc.mono sdiff_subset)
  have hsub : IsSubharmonicOn D f := by
    have hhq := (hh.mono hdc).sub (hq.mono (hdc.trans sdiff_subset))
    have hhqb := HarmonicOnNhd.sub_superharmonic hhq (hbc.mono (hdc.trans sdiff_subset)) hb
    convert hhqb using 1
  have hne : ∀ a ∈ K, ∀ᶠ y in 𝓝[D] a, f y < C := by
    intro a ha
    by_cases haρ : a ∈ closedBall c r
    · have hba := hbar a ⟨ha, haρ⟩
      have hba' : ∀ᶠ y in 𝓝[closedBall c r] a, M < b y :=
        (hbc a haρ).eventually (Ioi_mem_nhds hba)
      filter_upwards [hnear a ha, hba'.filter_mono
        (nhdsWithin_mono a (hdc.trans sdiff_subset))] with y hy hyb
      dsimp [f]
      linarith
    · have haway : ∀ᶠ y in 𝓝 a, y ∉ closedBall c r :=
        isClosed_closedBall.isOpen_compl.mem_nhds haρ
      filter_upwards [haway.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyD
      exact (hy (ball_subset_closedBall hyD.1)).elim
  have hle := isSubharmonicOn_ball_sdiff_le_of_eventually_lt hK hfc hsub hne
    (fun y hy hyK => by dsimp [f]; linarith [hbd y hy hyK, hbn y hy])
  intro y hy
  have := hle y hy
  dsimp [f] at this
  linarith

/-- A closed deletion with locally finite accumulation is removable for a
harmonic boundary comparison if the harmonic excess has a uniform local upper
bound at the deleted points. -/
theorem harmonic_sub_le_of_locally_finite_accumulation
    {R ρ C M : ℝ} {K L : Set ℂ} {h q : ℂ → ℝ} {x : ℂ}
    (hρR : ρ < R) (hKclosed : IsClosed K)
    (hL : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R → (L ∩ D).Finite)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R \ L → (K ∩ D).Finite)
    (hh : HarmonicOnNhd h (closedBall (0 : ℂ) ρ \ K))
    (hq : HarmonicOnNhd q (closedBall (0 : ℂ) ρ))
    (hM : 0 ≤ M)
    (hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball (0 : ℂ) ρ \ K] a, h y - q y ≤ C + M)
    (hbd : ∀ y ∈ sphere (0 : ℂ) ρ, y ∉ K → h y - q y ≤ C)
    (hx : x ∈ ball (0 : ℂ) ρ \ K) (hxL : x ∉ L) : h x - q x ≤ C := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨J₁, J₂, c₁, c₂, hJ₁, hJ₂, hc₁, hc₂, hsmall, hcover⟩ :=
    exists_cappedGreenBarrier_cover_of_locally_finite_accumulation
      (C := closedBall (0 : ℂ) ρ) (isCompact_closedBall _ _) (closedBall_subset_ball hρR)
      hL hK hx.2 hxL hM hε
  let b₁ : ℂ → ℝ := fun y => ∑ a ∈ J₁, cappedGreenBarrier R a c₁ (M + 1) y
  let b₂ : ℂ → ℝ := fun y => ∑ a ∈ J₂, cappedGreenBarrier R a c₂ (M + 1) y
  let b : ℂ → ℝ := fun y => b₁ y + b₂ y
  have hb₁ : ∀ y, 0 ≤ b₁ y := fun y => Finset.sum_nonneg fun a _ =>
    cappedGreenBarrier_nonneg hc₁.le (by linarith)
  have hb₂ : ∀ y, 0 ≤ b₂ y := fun y => Finset.sum_nonneg fun a _ =>
    cappedGreenBarrier_nonneg hc₂.le (by linarith)
  have hb₁c : ContinuousOn b₁ (closedBall (0 : ℂ) R) :=
    continuousOn_finsetSum J₁ (fun a ha => continuousOn_cappedGreenBarrier (hJ₁ ha) hc₁)
  have hb₂c : ContinuousOn b₂ (closedBall (0 : ℂ) R) :=
    continuousOn_finsetSum J₂ (fun a ha => continuousOn_cappedGreenBarrier (hJ₂ ha) hc₂)
  have hbc : ContinuousOn b (closedBall (0 : ℂ) ρ) :=
    (hb₁c.add hb₂c).mono ((closedBall_subset_ball hρR).trans ball_subset_closedBall)
  have h₁ := (laplacianLE_zero (0 : Measure ℂ) (ball (0 : ℂ) R)).add_finset_of_nonpos J₁
    (b := fun a => cappedGreenBarrier R a c₁ (M + 1))
    (fun a ha => laplacianLE_cappedGreenBarrier (hJ₁ ha) hc₁)
  have h₁' : LaplacianLE b₁ 0 (ball (0 : ℂ) R) := by simpa [b₁] using h₁
  have h₂ := h₁'.add_finset_of_nonpos J₂
    (b := fun a => cappedGreenBarrier R a c₂ (M + 1))
    (fun a ha => laplacianLE_cappedGreenBarrier (hJ₂ ha) hc₂)
  have hbΔ : LaplacianLE b 0 (ball (0 : ℂ) R) := by simpa [b, b₂] using h₂
  have hDopen : IsOpen (ball (0 : ℂ) ρ \ K) := isOpen_ball.sdiff hKclosed
  have hDR : ball (0 : ℂ) ρ \ K ⊆ ball (0 : ℂ) R :=
    sdiff_subset.trans (ball_subset_ball (le_of_lt hρR))
  have hbs : IsSuperharmonicOn (ball (0 : ℂ) ρ \ K) b :=
    superharmonicOfLaplacianLEStep_holds _ b hDopen
      (hbc.mono (sdiff_subset.trans ball_subset_closedBall)) (hbΔ.mono_set hDR)
  have hcmp := harmonic_sub_le_of_superharmonic_barrier hKclosed hh hq hbc hbs hnear
    (fun a ha => hcover a ⟨ha.1, ha.2⟩)
    (fun y _ => add_nonneg (hb₁ y) (hb₂ y)) hbd x hx
  dsimp [b, b₁, b₂] at hcmp
  linarith

/-- Away from the pole, the Newtonian obstacle gives one local upper bound
near every point of a closed deletion in a compact disc. -/
theorem IsHarmonicMinorant.exists_uniform_excess_near_closed_deletion
    {R ρ C : ℝ} {K : Set ℂ} {z : ℂ} {h q : ℂ → ℝ}
    (hρR : ρ < R) (hK : IsClosed K) (hzK : z ∉ K)
    (hh : IsHarmonicMinorant (ball (0 : ℂ) R \ K) (newtonKernelEReal z) h)
    (hq : HarmonicOnNhd q (closedBall (0 : ℂ) ρ)) :
    ∃ M ≥ 0, ∀ a ∈ K, ∀ᶠ y in 𝓝[ball (0 : ℂ) ρ \ K] a, h y - q y ≤ C + M := by
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.mp hK.isOpen_compl z hzK
  let T := closedBall (0 : ℂ) ρ \ ball z (δ / 2)
  have hTc : IsCompact T := (isCompact_closedBall (0 : ℂ) ρ).diff isOpen_ball
  have hTz : ∀ y ∈ T, y ≠ z := by
    intro y hy hyz
    apply hy.2
    rw [hyz]
    exact mem_ball_self (half_pos hδ)
  have hcont : ContinuousOn (fun y => newtonKernel z y - q y) T := by
    apply ContinuousOn.sub
    · intro y hy
      exact ((harmonicAt_newtonKernel (hTz y hy)).1.continuousAt).continuousWithinAt
    · exact hq.continuousOn.mono sdiff_subset
  obtain ⟨B, hB⟩ := hTc.exists_bound_of_continuousOn hcont
  let M := max (B - C) 0
  refine ⟨M, le_max_right _ _, ?_⟩
  intro a ha
  by_cases haρ : a ∈ closedBall (0 : ℂ) ρ
  · have haz : a ∉ closedBall z (δ / 2) := by
      intro haz
      have hain : a ∈ ball z δ :=
        closedBall_subset_ball (half_lt_self hδ) haz
      exact (hδK hain) ha
    have haway : ∀ᶠ y in 𝓝 a, y ∉ closedBall z (δ / 2) :=
      isClosed_closedBall.isOpen_compl.mem_nhds haz
    filter_upwards [haway.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyD
    have hyT : y ∈ T := ⟨ball_subset_closedBall hyD.1,
      fun hyb => hy (ball_subset_closedBall hyb)⟩
    have hyO : y ∈ ball (0 : ℂ) R \ K :=
      ⟨ball_subset_ball (le_of_lt hρR) hyD.1, hyD.2⟩
    have hyz := hTz y hyT
    have hobs : h y ≤ newtonKernel z y := by
      simpa [newtonKernelEReal, hyz] using hh.2 y hyO
    have hbound : newtonKernel z y - q y ≤ B :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB y hyT)
    have hM : B - C ≤ M := le_max_left _ _
    linarith
  · have haway : ∀ᶠ y in 𝓝 a, y ∉ closedBall (0 : ℂ) ρ :=
      isClosed_closedBall.isOpen_compl.mem_nhds haρ
    filter_upwards [haway.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyD
    exact (hy (ball_subset_closedBall hyD.1)).elim

/-- After deleting a closed set with locally finite accumulation, every
Newtonian harmonic minorant is bounded by the disc minorant away from the
accumulation set. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_locally_finite_accumulation
    {R : ℝ} {z x : ℂ} {K L : Set ℂ} (hKclosed : IsClosed K)
    (hL : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R → (L ∩ D).Finite)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R \ L → (K ∩ D).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K)
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) h)
    (hx : x ∈ ball (0 : ℂ) R \ K) (hxL : x ∉ L) :
    h x ≤ greatestHarmonicMinorantBall R z x := by
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
    have hq : HarmonicOnNhd (greatestHarmonicMinorantBall R z) (closedBall 0 ρ) :=
      (isHarmonicMinorant_greatestHarmonicMinorantBall hz.1).1.mono
        (closedBall_subset_ball hρR)
    obtain ⟨M, hM, hnear⟩ :=
      hh.exists_uniform_excess_near_closed_deletion hρR hKclosed hz.2 (C := B ρ) hq
    have hhρ : HarmonicOnNhd h (closedBall (0 : ℂ) ρ \ K) :=
      hh.1.mono (fun _ hy => ⟨closedBall_subset_ball hρR hy.1, hy.2⟩)
    apply harmonic_sub_le_of_locally_finite_accumulation hρR hKclosed hL hK hhρ hq hM hnear
      (x := x) ?_ ⟨mem_ball_zero_iff.mpr hxρ, hx.2⟩ hxL
    intro y hy hyK
    have hyn : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hy
    have hyz : y ≠ z := by rintro rfl; exact hzρ.ne hyn
    have hyR : ‖y‖ < R := hyn ▸ hρR
    have hpos := norm_sub_conj_mul_pos hR hzn hyR.le
    have h1 : h y ≤ newtonKernel z y := by
      have h := hh.2 y ⟨mem_ball_zero_iff.mpr hyR, hyK⟩
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

/-- The minorant comparison extends across the countable accumulation set at
points that were not deleted. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_accumulation
    {R : ℝ} {z x : ℂ} {K L : Set ℂ} (hKclosed : IsClosed K)
    (hL : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R → (L ∩ D).Finite)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R \ L → (K ∩ D).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K)
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) h)
    (hx : x ∈ ball (0 : ℂ) R \ K) :
    h x ≤ greatestHarmonicMinorantBall R z x := by
  let U := ball (0 : ℂ) R \ K
  have hU : IsOpen U := isOpen_ball.sdiff hKclosed
  have hcount : (L ∩ U).Countable :=
    (countable_inter_open_of_locally_finite isOpen_ball hL).mono
      (show L ∩ U ⊆ L ∩ ball (0 : ℂ) R from fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hcl : closure (U \ L) = closure U := closure_sdiff_countable_inter hU hcount
  have hxcl : x ∈ closure (U \ L) := hcl.symm ▸ subset_closure hx
  by_contra hnot
  have hgt : 0 < h x - greatestHarmonicMinorantBall R z x := sub_pos.mpr (not_le.mp hnot)
  have hcont := ((hh.1 x hx).1.continuousAt).sub
    (((isHarmonicMinorant_greatestHarmonicMinorantBall hz.1).1 x hx.1).1.continuousAt)
  have hev : ∀ᶠ y in 𝓝 x, 0 < h y - greatestHarmonicMinorantBall R z y :=
    hcont.eventually (Ioi_mem_nhds hgt)
  obtain ⟨y, hy, hygt⟩ := ((mem_closure_iff_frequently.mp hxcl).and_eventually hev).exists
  have hle := hh.le_greatestHarmonicMinorantBall_of_locally_finite_accumulation
    hKclosed hL hK hz hy.1 hy.2
  linarith

/-- The greatest harmonic minorant is unchanged at all points remaining after
a closed deletion with locally finite accumulation. -/
theorem greatestHarmonicMinorant_ball_sdiff_of_locally_finite_accumulation
    {R : ℝ} {z x : ℂ} {K L : Set ℂ} (hKclosed : IsClosed K)
    (hL : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R → (L ∩ D).Finite)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R \ L → (K ∩ D).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) :
    greatestHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) x =
      greatestHarmonicMinorantBall R z x := by
  apply le_antisymm
  · exact iSup₂_le fun _ hh => EReal.coe_le_coe_iff.mpr
      (hh.le_greatestHarmonicMinorantBall_of_accumulation hKclosed hL hK hz hx)
  · have hq := isHarmonicMinorant_greatestHarmonicMinorantBall hz.1
    have hq' : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z)
        (greatestHarmonicMinorantBall R z) :=
      ⟨fun y hy => hq.1 y hy.1, fun y hy => hq.2 y hy.1⟩
    exact hq'.le_greatestHarmonicMinorant x

/-- The disc Green function is preserved away from a closed deletion with
locally finite accumulation and away from the pole. -/
theorem greenFunction_ball_sdiff_of_locally_finite_accumulation
    {R : ℝ} {z x : ℂ} {K L : Set ℂ} (hKclosed : IsClosed K)
    (hL : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R → (L ∩ D).Finite)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R \ L → (K ∩ D).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    greenFunction (ball 0 R \ K) z x = greenFunction (ball 0 R) z x := by
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball_sdiff_of_locally_finite_accumulation hKclosed hL hK hz hx,
    EReal.toReal_coe, greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball hz.1 hx.1, EReal.toReal_coe]

#print axioms IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_accumulation
#print axioms greatestHarmonicMinorant_ball_sdiff_of_locally_finite_accumulation
#print axioms greenFunction_ball_sdiff_of_locally_finite_accumulation
#print axioms IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_locally_finite_accumulation
#print axioms IsHarmonicMinorant.exists_uniform_excess_near_closed_deletion
#print axioms harmonic_sub_le_of_locally_finite_accumulation
#print axioms harmonic_sub_le_of_superharmonic_barrier
#print axioms HarmonicOnNhd.sub_superharmonic
#print axioms isSubharmonicOn_ball_sdiff_le_of_eventually_lt

end HarmonicBalls

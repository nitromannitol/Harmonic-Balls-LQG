import HarmonicBalls.Proofs.Sec5.FiniteRankBarrierCover

/-! # Green functions after finite-rank point deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- A finite-rank closed set is removable for harmonic comparison when the
harmonic excess has a uniform local upper bound at the deleted points. -/
theorem harmonic_sub_le_of_locallyFiniteRank
    {R ρ C M : ℝ} {K : Set ℂ} {h q : ℂ → ℝ} {x : ℂ}
    (hρR : ρ < R) (hKclosed : IsClosed K)
    {n : ℕ} (hK : LocallyFiniteRank (ball (0 : ℂ) R) n K)
    (hh : HarmonicOnNhd h (closedBall (0 : ℂ) ρ \ K))
    (hq : HarmonicOnNhd q (closedBall (0 : ℂ) ρ)) (hM : 0 ≤ M)
    (hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball (0 : ℂ) ρ \ K] a, h y - q y ≤ C + M)
    (hbd : ∀ y ∈ sphere (0 : ℂ) ρ, y ∉ K → h y - q y ≤ C)
    (hx : x ∈ ball (0 : ℂ) ρ \ K) : h x - q x ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hbc, hbΔ, hbn, hbx, hbar⟩ :=
    exists_capped_barrier_of_locallyFiniteRank hKclosed hK
      (isCompact_closedBall _ _) (closedBall_subset_ball hρR) hx.2 hM hε
  have hbcρ : ContinuousOn b (closedBall (0 : ℂ) ρ) :=
    hbc.mono ((closedBall_subset_ball hρR).trans ball_subset_closedBall)
  have hDopen : IsOpen (ball (0 : ℂ) ρ \ K) := isOpen_ball.sdiff hKclosed
  have hDR : ball (0 : ℂ) ρ \ K ⊆ ball (0 : ℂ) R :=
    sdiff_subset.trans (ball_subset_ball (le_of_lt hρR))
  have hbs : IsSuperharmonicOn (ball (0 : ℂ) ρ \ K) b :=
    superharmonicOfLaplacianLEStep_holds _ b hDopen
      (hbcρ.mono (sdiff_subset.trans ball_subset_closedBall)) (hbΔ.mono_set hDR)
  have hcmp := harmonic_sub_le_of_superharmonic_barrier hKclosed hh hq hbcρ hbs hnear
    hbar (fun y _ => hbn y) hbd x hx
  linarith

/-- Every Newtonian harmonic minorant on the punctured disc is bounded by the
full-disc minorant at every undeleted point. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_of_locallyFiniteRank
    {R : ℝ} {z x : ℂ} {K : Set ℂ} (hKclosed : IsClosed K)
    {n : ℕ} (hK : LocallyFiniteRank (ball (0 : ℂ) R) n K)
    (hz : z ∈ ball (0 : ℂ) R \ K)
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) h)
    (hx : x ∈ ball (0 : ℂ) R \ K) :
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
    apply harmonic_sub_le_of_locallyFiniteRank hρR hKclosed hK hhρ hq hM hnear
      (x := x) ?_ ⟨mem_ball_zero_iff.mpr hxρ, hx.2⟩
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

theorem greatestHarmonicMinorant_ball_sdiff_of_locallyFiniteRank
    {R : ℝ} {z x : ℂ} {K : Set ℂ} (hKclosed : IsClosed K)
    {n : ℕ} (hK : LocallyFiniteRank (ball (0 : ℂ) R) n K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) :
    greatestHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) x =
      greatestHarmonicMinorantBall R z x := by
  apply le_antisymm
  · exact iSup₂_le fun _ hh => EReal.coe_le_coe_iff.mpr
      (hh.le_greatestHarmonicMinorantBall_of_locallyFiniteRank hKclosed hK hz hx)
  · have hq := isHarmonicMinorant_greatestHarmonicMinorantBall hz.1
    have hq' : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z)
        (greatestHarmonicMinorantBall R z) :=
      ⟨fun y hy => hq.1 y hy.1, fun y hy => hq.2 y hy.1⟩
    exact hq'.le_greatestHarmonicMinorant x

/-- The disc Green function is preserved away from a closed deletion with
locally finite accumulation and away from the pole. -/
theorem greenFunction_ball_sdiff_of_locallyFiniteRank
    {R : ℝ} {z x : ℂ} {K : Set ℂ} (hKclosed : IsClosed K)
    {n : ℕ} (hK : LocallyFiniteRank (ball (0 : ℂ) R) n K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    greenFunction (ball 0 R \ K) z x = greenFunction (ball 0 R) z x := by
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball_sdiff_of_locallyFiniteRank hKclosed hK hz hx,
    EReal.toReal_coe, greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball hz.1 hx.1, EReal.toReal_coe]


end HarmonicBalls

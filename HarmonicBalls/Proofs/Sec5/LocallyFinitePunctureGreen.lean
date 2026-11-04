import HarmonicBalls.Proofs.Sec5.FinitePunctureGreen

/-! # Green function after a locally finite point deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology InnerProductSpace

/-- A harmonic minorant after a locally finite point deletion is bounded by
its disc counterpart. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_locally_finite_punctured
    {R : ℝ} {z x : ℂ} (K : Set ℂ)
    (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
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
    let J : Finset ℂ := (hK ρ hρR).toFinset
    have hJ : (J : Set ℂ) = K ∩ closedBall (0 : ℂ) ρ := Set.Finite.coe_toFinset _
    have hKρ : (J : Set ℂ) ⊆ closedBall (0 : ℂ) ρ := by rw [hJ]; exact inter_subset_right
    have hKz : ∀ a ∈ J, a ≠ z := by
      intro a ha he
      apply hz.2
      have : a ∈ K := by
        have ha' : a ∈ (J : Set ℂ) := ha
        rw [hJ] at ha'
        exact ha'.1
      simpa [he] using this
    have hq : HarmonicOnNhd (greatestHarmonicMinorantBall R z) (closedBall 0 ρ) :=
      (isHarmonicMinorant_greatestHarmonicMinorantBall hz.1).1.mono
        (closedBall_subset_ball hρR)
    have hO : closedBall (0 : ℂ) ρ \ (J : Set ℂ) ⊆ ball 0 R \ K := by
      intro y hy
      refine ⟨closedBall_subset_ball hρR hy.1, ?_⟩
      intro hyK
      apply hy.2
      rw [hJ]
      exact ⟨hyK, hy.1⟩
    apply hh.sub_le_of_boundary_finset_punctured J hKz hKρ hO hq (C := B ρ) _ x
      ⟨mem_ball_zero_iff.mpr hxρ, fun hxJ => hx.2 ((hJ ▸ hxJ).1)⟩
    intro y hy hyK
    have hyn : ‖y‖ = ρ := mem_sphere_zero_iff_norm.mp hy
    have hyz : y ≠ z := by rintro rfl; exact hzρ.ne hyn
    have hyR : ‖y‖ < R := hyn ▸ hρR
    have hpos := norm_sub_conj_mul_pos hR hzn hyR.le
    have h1 : h y ≤ newtonKernel z y := by
      have hyK' : y ∉ K := by
        intro hy
        apply hyK
        change y ∈ (J : Set ℂ)
        rw [hJ]
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

/-- A locally finite deletion does not change the greatest harmonic minorant
on the remaining points of the disc. -/
theorem greatestHarmonicMinorant_locally_finite_punctured_ball {R : ℝ} {z x : ℂ}
    (K : Set ℂ) (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) :
    greatestHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z) x =
      greatestHarmonicMinorantBall R z x := by
  apply le_antisymm
  · exact iSup₂_le fun _ hh => EReal.coe_le_coe_iff.mpr
      (hh.le_greatestHarmonicMinorantBall_locally_finite_punctured K hK hz hx)
  · have hq := isHarmonicMinorant_greatestHarmonicMinorantBall hz.1
    have hq' : IsHarmonicMinorant (ball 0 R \ K) (newtonKernelEReal z)
        (greatestHarmonicMinorantBall R z) :=
      ⟨fun y hy => hq.1 y hy.1, fun y hy => hq.2 y hy.1⟩
    exact hq'.le_greatestHarmonicMinorant x

/-- Deleting points locally finite in the disc preserves its Green function
away from the pole and the deleted points. -/
theorem greenFunction_locally_finite_punctured_ball {R : ℝ} {z x : ℂ}
    (K : Set ℂ) (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    greenFunction (ball 0 R \ K) z x = greenFunction (ball 0 R) z x := by
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩,
    greatestHarmonicMinorant_locally_finite_punctured_ball K hK hz hx, EReal.toReal_coe,
    greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball hz.1 hx.1, EReal.toReal_coe]

#print axioms IsHarmonicMinorant.le_greatestHarmonicMinorantBall_locally_finite_punctured
#print axioms greatestHarmonicMinorant_locally_finite_punctured_ball
#print axioms greenFunction_locally_finite_punctured_ball

end HarmonicBalls

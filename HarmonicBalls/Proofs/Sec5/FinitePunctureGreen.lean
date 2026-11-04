import HarmonicBalls.Proofs.Sec5.FinitePunctureLogBarrier
import HarmonicBalls.Proofs.Sec5.PuncturedMinorantComparison
import HarmonicBalls.Proofs.Sec5.FinitePunctureCompetitorComparison

/-! # Green function of a finitely punctured disc -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology InnerProductSpace

/-- A harmonic minorant on a finitely punctured disc is bounded by the
greatest harmonic minorant on the whole disc. -/
theorem IsHarmonicMinorant.le_greatestHarmonicMinorantBall_finset_punctured
    {R : ℝ} {z x : ℂ} (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ))
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant (ball 0 R \ (K : Set ℂ)) (newtonKernelEReal z) h)
    (hx : x ∈ ball (0 : ℂ) R \ (K : Set ℂ)) :
    h x ≤ greatestHarmonicMinorantBall R z x := by
  classical
  have hzn : ‖z‖ < R := mem_ball_zero_iff.mp hz.1
  have hxn : ‖x‖ < R := mem_ball_zero_iff.mp hx.1
  have hR : 0 < R := (norm_nonneg z).trans_lt hzn
  have hKz : ∀ a ∈ K, a ≠ z := fun a ha he => hz.2 (he ▸ ha)
  let S : Finset ℝ := insert ‖z‖ (insert ‖x‖ (K.image fun a => ‖a‖))
  have hSne : S.Nonempty := ⟨‖z‖, by simp [S]⟩
  let m := S.max' hSne
  have hmR : m < R := by
    apply (Finset.max'_lt_iff S hSne).2
    intro y hy
    simp only [S, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | rfl | ⟨a, ha, rfl⟩
    · exact hzn
    · exact hxn
    · exact mem_ball_zero_iff.mp (hK ha)
  have hzm : ‖z‖ ≤ m := S.le_max' _ (by simp [S])
  have hxm : ‖x‖ ≤ m := S.le_max' _ (by simp [S])
  have hKm : ∀ a ∈ K, ‖a‖ ≤ m := fun a ha =>
    S.le_max' _ (by simp only [S, Finset.mem_insert, Finset.mem_image]; exact Or.inr (Or.inr ⟨a, ha, rfl⟩))
  let B : ℝ → ℝ := fun ρ =>
    (4 * Real.pi)⁻¹ * ((R ^ 2 - ‖z‖ ^ 2) * (R ^ 2 - ρ ^ 2) / (R ^ 2 * (ρ - ‖z‖) ^ 2))
  have hgB : ∀ ρ ∈ Ioo m R, h x - greatestHarmonicMinorantBall R z x ≤ B ρ := by
    rintro ρ ⟨hmρ, hρR⟩
    have hzρ : ‖z‖ < ρ := hzm.trans_lt hmρ
    have hxρ : ‖x‖ < ρ := hxm.trans_lt hmρ
    have hKρ : (K : Set ℂ) ⊆ closedBall (0 : ℂ) ρ := fun a ha =>
      mem_closedBall_zero_iff.mpr ((hKm a ha).trans hmρ.le)
    have hq : HarmonicOnNhd (greatestHarmonicMinorantBall R z) (closedBall 0 ρ) :=
      (isHarmonicMinorant_greatestHarmonicMinorantBall hz.1).1.mono
        (closedBall_subset_ball hρR)
    have hO : closedBall (0 : ℂ) ρ \ (K : Set ℂ) ⊆ ball 0 R \ (K : Set ℂ) :=
      fun _ hy => ⟨closedBall_subset_ball hρR hy.1, hy.2⟩
    apply hh.sub_le_of_boundary_finset_punctured K hKz hKρ hO hq (C := B ρ) _ x
      ⟨mem_ball_zero_iff.mpr hxρ, hx.2⟩
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

/-- Deleting finitely many points different from the pole preserves the
greatest harmonic minorant of the disc. -/
theorem greatestHarmonicMinorant_finset_punctured_ball {R : ℝ} {z x : ℂ}
    (K : Finset ℂ) (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ))
    (hx : x ∈ ball (0 : ℂ) R \ (K : Set ℂ)) :
    greatestHarmonicMinorant (ball 0 R \ (K : Set ℂ)) (newtonKernelEReal z) x =
      greatestHarmonicMinorantBall R z x := by
  apply le_antisymm
  · exact iSup₂_le fun _ hh => EReal.coe_le_coe_iff.mpr
      (hh.le_greatestHarmonicMinorantBall_finset_punctured K hK hz hx)
  · have hq := isHarmonicMinorant_greatestHarmonicMinorantBall hz.1
    have hq' : IsHarmonicMinorant (ball 0 R \ (K : Set ℂ)) (newtonKernelEReal z)
        (greatestHarmonicMinorantBall R z) :=
      ⟨fun y hy => hq.1 y hy.1, fun y hy => hq.2 y hy.1⟩
    exact hq'.le_greatestHarmonicMinorant x

/-- Deleting finitely many points different from the pole preserves the Green
function of the disc at all remaining points away from the pole. -/
theorem greenFunction_finset_punctured_ball {R : ℝ} {z x : ℂ}
    (K : Finset ℂ) (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ))
    (hx : x ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (hxz : x ≠ z) :
    greenFunction (ball 0 R \ (K : Set ℂ)) z x = greenFunction (ball 0 R) z x := by
  rw [greenFunction, ite_eq_left ⟨hz, hx, Ne.symm hxz⟩,
    greatestHarmonicMinorant_finset_punctured_ball K hK hz hx, EReal.toReal_coe,
    greenFunction, ite_eq_left ⟨hz.1, hx.1, Ne.symm hxz⟩,
    greatestHarmonicMinorant_ball hz.1 hx.1, EReal.toReal_coe]

/-- The disc cluster, with finitely many interior points deleted, is contained
in the cluster on the finitely punctured disc. -/
theorem disc_cluster_sdiff_subset_finite_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    (K : Finset ℂ) (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) :
    cluster μ R z t \ (K : Set ℂ) ⊆
      clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t :=
  disc_cluster_sdiff_subset_finite_punctured_of_green_eq hμ hR hV ht K
    (fun _ hx hxz => greenFunction_finset_punctured_ball K hK hz hx hxz)

#print axioms IsHarmonicMinorant.le_greatestHarmonicMinorantBall_finset_punctured
#print axioms greatestHarmonicMinorant_finset_punctured_ball
#print axioms greenFunction_finset_punctured_ball
#print axioms disc_cluster_sdiff_subset_finite_punctured

end HarmonicBalls

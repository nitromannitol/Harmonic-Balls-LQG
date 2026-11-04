import HarmonicBalls.Proofs.Sec6.LocalMollification
import HarmonicBalls.Proofs.Sec6.GreenDilation

/-! # Differentiating planar convolutions

These identities support local smooth approximation of subharmonic functions.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Laplacian
open scoped ContDiff Convolution

/-- A real directional derivative commutes with convolution by a smooth,
compactly supported kernel on the plane. -/
theorem directionalDeriv_convolution_left {k g : ℂ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hg : LocallyIntegrable g volume) (v : ℂ) :
    (fun z => fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) z v) =
      ((fun z => fderiv ℝ k z v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  funext x
  have hderiv :
      fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
        ((fderiv ℝ k ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ, volume] g) x) :=
    (hkc.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume) (hf := hk.of_le (by norm_num)) hg x).fderiv
  rw [hderiv]
  calc
    ((fderiv ℝ k ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ, volume] g) x) v
        = ((g ⋆[((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℂ).flip, volume]
            fderiv ℝ k) x) v := by rw [convolution_flip]
    _ = ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip.precompR ℂ, volume]
            fderiv ℝ k) x) v := rfl
    _ = (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume]
            (fun y => (fderiv ℝ k y) v)) x :=
          convolution_precompR_apply (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
            (f := g) (g := fderiv ℝ k) (μ := volume) hg (hkc.fderiv ℝ)
            (hk.continuous_fderiv (by norm_num)) x v
    _ = ((fun y => (fderiv ℝ k y) v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
          rw [convolution_flip]

/-- The planar Laplacian commutes with convolution by a smooth compactly
supported kernel. -/
theorem laplacian_convolution_left {k g : ℂ → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (hg : LocallyIntegrable g volume) :
    Δ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      ((Δ k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  have hd : ∀ v : ℂ, ContDiff ℝ ∞ (fun z => fderiv ℝ k z v) := by
    intro v
    exact (hk.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hc : ∀ v : ℂ, HasCompactSupport (fun z => fderiv ℝ k z v) :=
    fun v => hkc.fderiv_apply ℝ v
  have hconv : ContDiff ℝ ∞ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    hkc.contDiff_convolution_left _ hk hg
  have hsecond : ∀ v : ℂ,
      (fun z => fderiv ℝ (fun y =>
        fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y v) z v) =
      ((fun z => fderiv ℝ (fun y => fderiv ℝ k y v) z v) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
    intro v
    rw [directionalDeriv_convolution_left hk hkc hg v]
    exact directionalDeriv_convolution_left (hd v) (hc v) hg v
  have hsecond_smooth : ∀ v : ℂ,
      ContDiff ℝ ∞ (fun z => fderiv ℝ (fun y => fderiv ℝ k y v) z v) := by
    intro v
    exact ((hd v).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hsecond_compact : ∀ v : ℂ,
      HasCompactSupport (fun z => fderiv ℝ (fun y => fderiv ℝ k y v) z v) :=
    fun v => (hc v).fderiv_apply ℝ v
  funext z
  rw [laplacian_eq_fderiv_fderiv (hconv.of_le (by norm_num))]
  have ha := congrFun (hsecond 1) z
  have hb := congrFun (hsecond Complex.I) z
  rw [ha, hb, convolution_def, convolution_def, convolution_def]
  have hi : ∀ v : ℂ, Integrable (fun t =>
      ContinuousLinearMap.lsmul ℝ ℝ (fderiv ℝ (fun y => fderiv ℝ k y v) t v) (g (z - t))) := by
    intro v
    exact ((hsecond_compact v).convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hf := (hsecond_smooth v).continuous) (hg := hg) z).integrable
  rw [← integral_add (hi 1) (hi Complex.I)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [laplacian_eq_fderiv_fderiv (hk.of_le (by norm_num))]
  ring

/-- Sufficiently local mollification of a distributionally subharmonic
function has nonnegative classical Laplacian on the compact set. -/
theorem laplacian_mollify_nonneg
    {U K : Set ℂ} {q g : ℂ → ℝ} (hq : LaplacianGE q 0 U)
    (hgc : Continuous g) {δ : ℝ} (hδU : Metric.cthickening δ K ⊆ U)
    (hgeq : EqOn g q (Metric.cthickening δ K))
    {z : ℂ} (hz : z ∈ K) {n : ℕ} (hn : (mollifierBump n).rOut ≤ δ) :
    0 ≤ Δ (mollify n g) z := by
  let ρ : ℂ → ℝ := (mollifierBump n).normed volume
  have heven : (fun x => ρ (-x)) = ρ := by
    funext x
    exact (mollifierBump n).normed_neg x
  have hΔeven (x : ℂ) : Δ ρ (-x) = Δ ρ x := by
    have h := laplacian_comp_real_dilation ρ (k := -1) (by norm_num) x
    simp only [neg_one_smul, neg_one_sq, one_mul, heven] at h
    exact h.symm
  have hpair := mollifier_laplacian_pairing_nonneg hq hδU hgeq hz hn
  change 0 ≤ ∫ t, g t * Δ ρ (t - z) at hpair
  unfold mollify
  rw [laplacian_convolution_left (mollifierBump n).contDiff_normed
    (mollifierBump n).hasCompactSupport_normed hgc.locallyIntegrable]
  rw [← convolution_flip, convolution_def]
  convert hpair using 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← hΔeven (z - t), neg_sub]
  ring

/-- A continuous subharmonic function admits smooth, compactly supported
approximations with nonnegative Laplacian on each compact subset of its domain. -/
theorem exists_compactlySupported_smooth_subharmonic_approximation
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : ℂ → ℝ} (hq : ContinuousOn q U) (hsub : IsSubharmonicOn U q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ z ∈ K, |f z - q z| ≤ ε) ∧ ∀ z ∈ K, 0 ≤ Δ f z := by
  have hqΔ : LaplacianGE q 0 U := LaplacianGE.of_laplacianLE_neg
    (laplacianLEOfSuperharmonicStep_holds U (-q) hU hq.neg hsub)
  obtain ⟨g, hgc, hgs, hgU, hgq, ⟨δ, hδ, hδU, hgeq⟩, happrox⟩ :=
    exists_local_mollification hU hK hKU hq
  obtain ⟨N, hN⟩ := happrox ε hε δ hδ
  obtain ⟨hsm, hsupp, hclose, hr⟩ := hN N le_rfl
  refine ⟨mollify N g, hsm, hsupp, hclose, ?_⟩
  intro z hz
  exact laplacian_mollify_nonneg hqΔ hgc hδU hgeq hz hr.le

end HarmonicBalls.Section6

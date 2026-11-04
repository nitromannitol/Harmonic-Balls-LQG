import HarmonicBalls.Proofs.Sec8.LogarithmicPotentialDecay

/-! # Localization of logarithmic potential energy

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

open MeasureTheory Metric Set Laplacian Filter
open scoped Topology ContDiff

namespace HarmonicBalls

/-- The directional integration-by-parts identity behind localization of
Dirichlet energy. Only the cutoff is required to have compact support. -/
theorem integral_directional_cutoff_energy {u η : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (v : ℂ) :
    (∫ x, (fderiv ℝ (fun y => η y * u y) x v) ^ 2 +
      (η x * η x * u x) * fderiv ℝ (fun y => fderiv ℝ u y v) x v) =
      ∫ x, (u x * fderiv ℝ η x v) ^ 2 := by
  let f : ℂ → ℝ := fun x => η x * η x * u x
  let g : ℂ → ℝ := fun x => fderiv ℝ u x v
  let p : ℂ → ℝ := fun x => η x * u x
  have hf : ContDiff ℝ 2 f := (hη.mul hη).mul hu
  have hfc : HasCompactSupport f := (hηc.mul_right).mul_right
  have hg : ContDiff ℝ 1 g := (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hp : ContDiff ℝ 2 p := hη.mul hu
  have hpc : HasCompactSupport p := hηc.mul_right
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdp : Continuous (fun x => fderiv ℝ p x v) :=
    (hp.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have i1 : Integrable (fun x => fderiv ℝ f x v * g x) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v).mul_right
  have i2 : Integrable (fun x => f x * fderiv ℝ g x v) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport hfc.mul_right
  have i3 : Integrable (fun x => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have ip : Integrable (fun x => (fderiv ℝ p x v) ^ 2) :=
    (hdp.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two] using (hpc.fderiv_apply ℝ v).mul_right
        (f' := fun x => fderiv ℝ p x v))
  have hparts : (∫ x, f x * fderiv ℝ g x v) =
      -(∫ x, fderiv ℝ f x v * g x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
      (fun x _ => (hf.differentiable (by norm_num)) x)
      (fun x _ => (hg.differentiable one_ne_zero) x)
  change (∫ x, (fderiv ℝ p x v) ^ 2 + f x * fderiv ℝ g x v) = _
  rw [integral_add ip i2, hparts, ← sub_eq_add_neg, ← integral_sub ip i1]
  apply integral_congr_ae
  filter_upwards with x
  have hdu := (hu.differentiable (by norm_num)) x
  have hdη := (hη.differentiable (by norm_num)) x
  have hdηη := ((hη.mul hη).differentiable (by norm_num)) x
  dsimp only [p, f, g]
  rw [fderiv_fun_mul hdη hdu, fderiv_fun_mul hdηη hdu, fderiv_fun_mul hdη hdη]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Localization of planar Dirichlet energy by a smooth compact cutoff. -/
theorem integral_cutoff_dirichlet_energy {u η : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    (∫ x, (fderiv ℝ (fun y => η y * u y) x 1) ^ 2 +
        (fderiv ℝ (fun y => η y * u y) x Complex.I) ^ 2 +
        (η x * η x * u x) * Δ u x) =
      ∫ x, u x ^ 2 * ((fderiv ℝ η x 1) ^ 2 + (fderiv ℝ η x Complex.I) ^ 2) := by
  let p : ℂ → ℝ := fun x => η x * u x
  let f : ℂ → ℝ := fun x => η x * η x * u x
  have hp : ContDiff ℝ 2 p := hη.mul hu
  have hpc : HasCompactSupport p := hηc.mul_right
  have hf : ContDiff ℝ 2 f := (hη.mul hη).mul hu
  have hfc : HasCompactSupport f := hηc.mul_right.mul_right
  have idir : ∀ v : ℂ, Integrable (fun x => (fderiv ℝ p x v) ^ 2 +
      f x * fderiv ℝ (fun y => fderiv ℝ u y v) x v) := by
    intro v
    have hdp : Continuous (fun x => fderiv ℝ p x v) :=
      (hp.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdu : ContDiff ℝ 1 (fun x => fderiv ℝ u x v) :=
      (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hddu : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ u y v) x v) :=
      (hdu.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have ip : Integrable (fun x => (fderiv ℝ p x v) ^ 2) :=
      (hdp.pow 2).integrable_of_hasCompactSupport (by
        simpa only [pow_two] using (hpc.fderiv_apply ℝ v).mul_right
          (f' := fun x => fderiv ℝ p x v))
    exact ip.add ((hf.continuous.mul hddu).integrable_of_hasCompactSupport hfc.mul_right)
  have igrad : ∀ v : ℂ, Integrable (fun x => (u x * fderiv ℝ η x v) ^ 2) := by
    intro v
    have hdη : Continuous (fun x => fderiv ℝ η x v) :=
      (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hc : HasCompactSupport (fun x => u x * fderiv ℝ η x v) :=
      (hηc.fderiv_apply ℝ v).mul_left
    exact ((hu.continuous.mul hdη).pow 2).integrable_of_hasCompactSupport (by
      convert hc.mul_right (f' := fun x => u x * fderiv ℝ η x v) using 1
      ext x
      simp only [Pi.mul_apply, pow_two])
  have h1 := integral_directional_cutoff_energy hu hη hηc 1
  have hI := integral_directional_cutoff_energy hu hη hηc Complex.I
  have hsum := congrArg₂ (· + ·) h1 hI
  change (∫ x, (fderiv ℝ p x 1) ^ 2 + f x *
      fderiv ℝ (fun y => fderiv ℝ u y 1) x 1) +
    (∫ x, (fderiv ℝ p x Complex.I) ^ 2 + f x *
      fderiv ℝ (fun y => fderiv ℝ u y Complex.I) x Complex.I) = _ at hsum
  rw [← integral_add (idir 1) (idir Complex.I),
    ← integral_add (igrad 1) (igrad Complex.I)] at hsum
  calc
    _ = ∫ x, ((fderiv ℝ p x 1) ^ 2 + f x *
        fderiv ℝ (fun y => fderiv ℝ u y 1) x 1) +
        ((fderiv ℝ p x Complex.I) ^ 2 + f x *
        fderiv ℝ (fun y => fderiv ℝ u y Complex.I) x Complex.I) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [laplacian_eq_fderiv_fderiv hu]
      ring
    _ = _ := by
      rw [hsum]
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- The covariance error for a cutoff of the logarithmic potential depends
on the cutoff-gradient energy and compactly supported source integrals. -/
theorem IsWholePlaneGFF.laplacian_cutoff_covariance_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ η : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : ∫ x, φ x = 0)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hΔ : IsTestFunction univ (Δ (fun x => η x * planarLogPotential φ x))) :
    wholePlaneGFFCov (.pairing (Δ (fun x => η x * planarLogPotential φ x)))
        (.pairing (Δ (fun x => η x * planarLogPotential φ x))) +
      wholePlaneGFFCov (.pairing φ) (.pairing φ) -
      2 * wholePlaneGFFCov (.pairing (Δ (fun x => η x * planarLogPotential φ x)))
        (.pairing φ) =
      2 * Real.pi * ((∫ x, (planarLogPotential φ x) ^ 2 *
        ((fderiv ℝ η x 1) ^ 2 + (fderiv ℝ η x Complex.I) ^ 2)) -
        (∫ x, (η x * η x * planarLogPotential φ x) * φ x) -
        (∫ x, φ x * planarLogPotential φ x) +
        2 * ∫ x, φ x * (η x * planarLogPotential φ x)) := by
  let u := planarLogPotential φ
  let ψ : ℂ → ℝ := fun x => η x * u x
  have hu : ContDiff ℝ 2 u := (contDiff_planarLogPotential hφ).of_le (by norm_num)
  have hψ : ContDiff ℝ 2 ψ := (hη.of_le (by norm_num)).mul hu
  have hψc : HasCompactSupport ψ := hηc.mul_right
  have hΔu : Δ u = φ := laplacian_planarLogPotential hφ
  have hcont : ∀ v : ℂ, Continuous (fun x => fderiv ℝ ψ x v) := by
    intro v
    exact (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi : ∀ v : ℂ, Integrable (fun x => (fderiv ℝ ψ x v) ^ 2) := by
    intro v
    exact ((hcont v).pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two] using (hψc.fderiv_apply ℝ v).mul_right
        (f' := fun x => fderiv ℝ ψ x v))
  have isource : Integrable (fun x => (η x * η x * u x) * Δ u x) :=
    ((((hη.continuous.mul hη.continuous).mul hu.continuous).mul
      (continuous_laplacian_of_contDiff hu)).integrable_of_hasCompactSupport
        hηc.mul_right.mul_right.mul_right)
  have henergy := integral_cutoff_dirichlet_energy hu (hη.of_le (by norm_num)) hηc
  change (∫ x, (fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2 +
      (η x * η x * u x) * Δ u x) = _ at henergy
  have hsplit : (∫ x, (fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2 +
      (η x * η x * u x) * Δ u x) =
      (∫ x, (fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2) +
        ∫ x, (η x * η x * u x) * Δ u x := by
    simpa only [Pi.add_apply] using integral_add ((hi 1).add (hi Complex.I)) isource
  rw [hsplit, hΔu] at henergy
  have hψenergy : (∫ x, Δ ψ x * ψ x) =
      -(∫ x, (fderiv ℝ ψ x 1) ^ 2 + (fderiv ℝ ψ x Complex.I) ^ 2) := by
    calc
      _ = ∫ x, ψ x * Δ ψ x := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := integral_mul_laplacian_eq_neg_dirichlet_energy hψ hψc
  change wholePlaneGFFCov (.pairing (Δ ψ)) (.pairing (Δ ψ)) +
    wholePlaneGFFCov (.pairing φ) (.pairing φ) -
    2 * wholePlaneGFFCov (.pairing (Δ ψ)) (.pairing φ) = _
  rw [h.laplacian_covariance_error_eq_logPotential hφ hφzero hψ hψc hΔ, hψenergy]
  dsimp only [u, ψ] at henergy ⊢
  rw [← henergy]
  ring

end HarmonicBalls

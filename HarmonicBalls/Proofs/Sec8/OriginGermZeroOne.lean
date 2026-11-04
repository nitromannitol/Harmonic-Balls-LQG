import HarmonicBalls.Proofs.Sec8.WeightedPuncturedCutoffEnergy
import HarmonicBalls.Proofs.Sec8.PuncturedFieldGeneration
/-! # Triviality of the whole-plane field germ

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb formalization. -/

open MeasureTheory Set Metric Filter Real Laplacian
open scoped Topology Real ContDiff
namespace HarmonicBalls

/-- The Laplacian of a smooth function on the complex plane is smooth. -/
theorem contDiff_laplacian_of_smooth {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Δ φ) := by
  have hφ1 : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by simp)
  have h (v : ℂ) : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => fderiv ℝ φ z v) y v) :=
    (((hφ1.clm_apply contDiff_const).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have he : Δ φ = fun y => fderiv ℝ (fun z => fderiv ℝ φ z 1) y 1 +
      fderiv ℝ (fun z => fderiv ℝ φ z Complex.I) y Complex.I :=
    funext (laplacian_eq_fderiv_fderiv (hφ.of_le (by simp)))
  rw [he]
  exact (h 1).add (h Complex.I)

/-- Mean-zero tests are approximated in covariance by punctured Laplacian probes. -/
theorem IsWholePlaneGFF.punctured_laplacian_covariance_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (φ : ℂ → ℝ)
    (hφ : IsTestFunction univ φ) (hφzero : ∫ x, φ x = 0) :
    ∃ ψ : ℕ → ℂ → ℝ, (∀ k, IsTestFunction univ (ψ k) ∧
      IsTestFunction univ (Δ (ψ k)) ∧ ∃ n : ℕ,
        ∀ x ∈ ball (0 : ℂ) (((n : ℝ) + 1)⁻¹), ψ k x = 0) ∧
      Tendsto (fun k => wholePlaneGFFCov (.pairing (Δ (ψ k))) (.pairing (Δ (ψ k))) +
        wholePlaneGFFCov (.pairing φ) (.pairing φ) -
        2 * wholePlaneGFFCov (.pairing (Δ (ψ k))) (.pairing φ)) atTop (𝓝 0) := by
  let u := planarLogPotential φ
  let ψ : ℕ → ℂ → ℝ := fun k x => puncturedCutoff k x * u x
  have hu : ContDiff ℝ ∞ u := contDiff_planarLogPotential hφ
  have hψ (k : ℕ) : ContDiff ℝ ∞ (ψ k) := (contDiff_puncturedCutoff k).mul hu
  have hψc (k : ℕ) : HasCompactSupport (ψ k) := (hasCompactSupport_puncturedCutoff k).mul_right
  have htest (k : ℕ) : IsTestFunction univ (ψ k) := ⟨hψ k, hψc k, subset_univ _⟩
  have hΔtest (k : ℕ) : IsTestFunction univ (Δ (ψ k)) :=
    ⟨contDiff_laplacian_of_smooth (hψ k), hasCompactSupport_laplacian (hψc k), subset_univ _⟩
  have hsource : Integrable (fun z => φ z * u z) :=
    (hφ.1.continuous.mul hu.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hs2 : Tendsto (fun k : ℕ => ∫ z, (puncturedCutoff k z * puncturedCutoff k z * u z) * φ z)
      atTop (𝓝 (∫ z, φ z * u z)) := by
    have hh := tendsto_integral_mul_puncturedCutoff_pow hsource 2
    convert hh using 1
    funext k
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have hs1 : Tendsto (fun k : ℕ => ∫ z, φ z * (puncturedCutoff k z * u z))
      atTop (𝓝 (∫ z, φ z * u z)) := by
    have hh := tendsto_integral_mul_puncturedCutoff_pow hsource 1
    convert hh using 1
    funext k
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have he := tendsto_integral_planarLogPotential_puncturedCutoff_gradient hφ hφzero
  refine ⟨ψ, ?_, ?_⟩
  · intro k
    refine ⟨htest k, hΔtest k, ?_⟩
    obtain ⟨n, hn⟩ := puncturedCutoff_eq_zero_near_zero k
    exact ⟨n, fun x hx => by simp [ψ, hn x hx]⟩
  · have hc : Tendsto (fun _ : ℕ => (2 * Real.pi)) atTop (𝓝 (2 * Real.pi)) := tendsto_const_nhds
    have ha : Tendsto (fun _ : ℕ => (∫ z, φ z * u z)) atTop (𝓝 (∫ z, φ z * u z)) := tendsto_const_nhds
    have ht : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 (2 : ℝ)) := tendsto_const_nhds
    have hlim := hc.mul (((he.sub hs2).sub ha).add (ht.mul hs1))
    have hlim' : Tendsto (fun k : ℕ => 2 * Real.pi *
        ((∫ z, u z ^ 2 * ((fderiv ℝ (puncturedCutoff k) z 1) ^ 2 +
          (fderiv ℝ (puncturedCutoff k) z Complex.I) ^ 2)) -
          (∫ z, (puncturedCutoff k z * puncturedCutoff k z * u z) * φ z) -
          (∫ z, φ z * u z) + 2 * ∫ z, φ z * (puncturedCutoff k z * u z))) atTop (𝓝 0) := by
      convert hlim using 1; ring
    apply hlim'.congr'
    filter_upwards [] with k
    exact (h.laplacian_cutoff_covariance_error hφ hφzero (contDiff_puncturedCutoff k)
      (hasCompactSupport_puncturedCutoff k) (hΔtest k)).symm

/-- The germ of the whole-plane GFF modulo constants at the origin is trivial. -/
theorem IsWholePlaneGFF.origin_germ_trivial
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 :=
  h.origin_germ_trivial_of_laplacian_covariance_approximation α₀
    h.punctured_laplacian_covariance_approximation

end HarmonicBalls

import HarmonicBalls.Proofs.Sec8.ExteriorLaplacianGerm
import HarmonicBalls.Proofs.Sec8.CirclePairingCovariance

/-! # Generating the punctured field from Laplacian pairings

The probabilistic reduction uses Leonardo Bonanno's LatticeProb formalization
of the ergodic theorem through its Section 8 imports. -/

open MeasureTheory ProbabilityTheory Metric Set Laplacian Filter
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- Sets with an almost surely equal representative in a specified σ-algebra. -/
@[instance_reducible]
noncomputable def aeRepresentativeSigma {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B : Set Ω, MeasurableSet[m] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, MeasurableSet.empty, .rfl⟩
  measurableSet_compl := by
    intro A hA
    obtain ⟨B, hB, hAB⟩ := hA
    exact ⟨Bᶜ, hB.compl, hAB.compl⟩
  measurableSet_iUnion := by
    intro A hA
    choose B hB hAB using hA
    refine ⟨⋃ n, B n, MeasurableSet.iUnion hB, ?_⟩
    filter_upwards [ae_all_iff.2 hAB] with ω hω
    simp only [mem_iUnion]
    exact propext (exists_congr fun n => iff_of_eq (hω n))

/-- Each exterior Laplacian pairing is measurable for the punctured probe
σ-algebra when the potential vanishes on a neighborhood of the origin. -/
theorem measurable_puncturedLaplacian_pairing {Ω : Type*}
    (hC : Ω → (ℂ → ℝ) → ℝ) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction Set.univ ψ ∧ IsTestFunction Set.univ (Δ ψ))
    (n : ℕ) (hvanish : ∀ x ∈ ball (0 : ℂ) (((n : ℝ) + 1)⁻¹), ψ x = 0) :
    @Measurable Ω ℝ (puncturedLaplacianSigma hC) _ (fun ω => hC ω (Δ ψ)) := by
  apply measurable_iff_comap_le.2
  unfold puncturedLaplacianSigma exteriorLaplacianSigma
  exact le_iSup_of_le n (le_iSup_of_le ψ (le_iSup_of_le ⟨hψ.1, hψ.2, hvanish⟩ le_rfl))

/-- Approximation in probability of every mean-zero test pairing by punctured
Laplacian pairings yields completed generation of the whole field modulo constants. -/
theorem completed_field_generation_of_laplacian_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (α₀ : ℝ)
    (happrox : ∀ (φ : ℂ → ℝ), IsTestFunction Set.univ φ → (∫ x, φ x) = 0 →
      ∃ ψ : ℕ → ℂ → ℝ, (∀ k, IsTestFunction Set.univ (ψ k) ∧
        IsTestFunction Set.univ (Δ (ψ k)) ∧ ∃ n : ℕ,
          ∀ x ∈ ball (0 : ℂ) (((n : ℝ) + 1)⁻¹), ψ k x = 0) ∧
        TendstoInMeasure P (fun k ω => hC ω (Δ (ψ k))) atTop (fun ω => hC ω φ)) :
    ∀ A : Set Ω, MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC Set.univ] A →
      ∃ B : Set Ω, MeasurableSet[puncturedLaplacianSigma hC] B ∧ A =ᵐ[P] B := by
  have hle : Section6.fieldSigmaAlgebraModConst α₀ hC Set.univ ≤
      aeRepresentativeSigma P (puncturedLaplacianSigma hC) := by
    unfold Section6.fieldSigmaAlgebraModConst
    refine iSup_le fun φ => iSup_le fun hφ => ?_
    obtain ⟨ψ, hψ, hlim⟩ := happrox φ hφ.1 hφ.2
    have hm (k : ℕ) : @Measurable Ω ℝ (puncturedLaplacianSigma hC) _
        (fun ω => hC ω (Δ (ψ k))) := by
      obtain ⟨n, hn⟩ := (hψ k).2.2
      exact measurable_puncturedLaplacian_pairing hC (ψ k) ⟨(hψ k).1, (hψ k).2.1⟩ n hn
    obtain ⟨g, hg, hge⟩ := exists_measurable_version_of_tendstoInMeasure
      (puncturedLaplacianSigma hC) _ _ hm hlim
    apply measurable_iff_comap_le.1
    intro s hs
    refine ⟨(fun ω => g ω - α₀ * ∫ x, φ x * Real.log ‖x‖) ⁻¹' s,
      (hg.sub_const _) hs, ?_⟩
    filter_upwards [hge] with ω hω
    simp only [mem_preimage, fieldPairing, hω]
  intro A hA
  exact hle A hA

/-- A vanishing covariance-kernel error implies convergence in probability of
whole-plane GFF pairings. -/
theorem IsWholePlaneGFF.tendstoInMeasure_pairing_of_covariance_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ)
    (q : ℕ → ℂ → ℝ) (hq : ∀ n, IsTestFunction univ (q n))
    (hcov : Tendsto (fun n => wholePlaneGFFCov (.pairing (q n)) (.pairing (q n)) +
      wholePlaneGFFCov (.pairing φ) (.pairing φ) -
      2 * wholePlaneGFFCov (.pairing (q n)) (.pairing φ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => hC ω (q n)) atTop (fun ω => hC ω φ) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hp : MemLp (fun ω => hC ω φ) 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hqLp (n : ℕ) : MemLp (fun ω => hC ω (q n)) 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing (q n), hq n⟩ : GFFObservable.Admissible)).memLp (by simp)
  apply tendstoInMeasure_of_centered_variance_tendsto_zero P _ _ (fun n => (hqLp n).sub hp)
  · intro n
    rw [integral_sub ((hqLp n).integrable (by norm_num)) (hp.integrable (by norm_num))]
    have h1 := h.integral_eq_zero (.pairing (q n)) (hq n)
    have h2 := h.integral_eq_zero (.pairing φ) hφ
    simp only [GFFObservable.eval] at h1 h2
    rw [h1, h2, sub_self]
  · convert hcov using 1
    funext n
    change variance ((fun ω => hC ω (q n)) - (fun ω => hC ω φ)) P = _
    rw [variance_sub (hqLp n) hp, ← covariance_self (hqLp n).aemeasurable,
      ← covariance_self hp.aemeasurable]
    have h1 := h.covariance_eq (.pairing (q n)) (.pairing (q n)) (hq n) (hq n)
    have h2 := h.covariance_eq (.pairing φ) (.pairing φ) hφ hφ
    have h3 := h.covariance_eq (.pairing (q n)) (.pairing φ) (hq n) hφ
    simp only [GFFObservable.eval] at h1 h2 h3
    rw [h1, h2, h3]
    ring

/-- The origin germ is trivial if each mean-zero test is approximated in the
GFF covariance seminorm by Laplacians of compact potentials vanishing near
the origin. -/
theorem IsWholePlaneGFF.origin_germ_trivial_of_laplacian_covariance_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ)
    (happrox : ∀ (φ : ℂ → ℝ), IsTestFunction Set.univ φ → (∫ x, φ x) = 0 →
      ∃ ψ : ℕ → ℂ → ℝ, (∀ k, IsTestFunction Set.univ (ψ k) ∧
        IsTestFunction Set.univ (Δ (ψ k)) ∧ ∃ n : ℕ,
          ∀ x ∈ ball (0 : ℂ) (((n : ℝ) + 1)⁻¹), ψ k x = 0) ∧
        Tendsto (fun k => wholePlaneGFFCov (.pairing (Δ (ψ k))) (.pairing (Δ (ψ k))) +
          wholePlaneGFFCov (.pairing φ) (.pairing φ) -
          2 * wholePlaneGFFCov (.pairing (Δ (ψ k))) (.pairing φ)) atTop (𝓝 0)) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  apply h.origin_germ_trivial_of_exterior_generation α₀
  apply completed_field_generation_of_laplacian_approximation P hC α₀
  intro φ hφ hzero
  obtain ⟨ψ, hψ, hcov⟩ := happrox φ hφ hzero
  refine ⟨ψ, hψ, ?_⟩
  exact h.tendstoInMeasure_pairing_of_covariance_error φ hφ
    (fun k => Δ (ψ k)) (fun k => (hψ k).2.1) hcov

end HarmonicBalls

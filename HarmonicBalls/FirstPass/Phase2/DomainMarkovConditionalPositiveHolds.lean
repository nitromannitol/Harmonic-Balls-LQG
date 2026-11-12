import HarmonicBalls.FirstPass.Phase2.DomainMarkovCircleVariance
import HarmonicBalls.FirstPass.Phase2.DomainMarkovDualSummable
import HarmonicBalls.FirstPass.Phase2.DomainMarkovDualFamily
import HarmonicBalls.FirstPass.Phase2.DomainMarkovReduction
import HarmonicBalls.FirstPass.Frozen.S11k
import LatticeProb.Prob.CovarianceRegression
import LatticeProb.Gauss.ConditionalEquivalence

/-! # Domain Markov property of the whole-plane GFF: positivity of conditional probabilities

Let `W = B(c, r)` and let `O` be open with `closure O ⊆ W`. An event of positive probability measurable for the field on
`O` has almost surely positive conditional probability given the field outside `closure W` modulo additive constants.

The proof combines the reduction to countably many inner pairings and pairwise uncorrelated mean-zero outer pairings
(`IsWholePlaneGFF.ae_condExp_indicator_pos_of_orthogonal_core`) with the conditional equivalence for a Gaussian family
with a dual family (`LatticeProb.Gauss.measure_inter_eq_zero_of_dual_family`). For a cutoff `χ` on `W` equal to `1` on
`O`, the dual coordinates are the Laplacian pairings `(h, Δφ_ρ)` (`dualTest χ ρ`): they are uncorrelated with every
outer pairing and have the covariances of `(h, ρ)` with every inner pairing. Summability of the weighted variances
follows from Bessel's inequality for the circle averages `h_ε(x)`, `x ∈ supp χ`, whose covariances with the outer
pairings are the covariance potentials `outerPotential ρ x`.

## Main results

* `IsWholePlaneGFF.variance_pairing`: `Var((h, ρ)) = G(ρ, ρ)`.
* `IsWholePlaneGFF.exists_sum_inv_cov_mul_outerPotential_sq_le`: Bessel's bound
  `∑_k G(ρ_k, ρ_k)⁻¹ (G ρ_k)(x)² ≤ M` on a compact `K ⊆ W` for pairwise uncorrelated mean-zero outer tests.
* `IsWholePlaneGFF.measure_inter_eq_zero_or_of_ball`: the null-intersection statement for inner and orthogonal outer
  coordinates.
* `domainMarkovConditionalPositive_holds`: the input `DomainMarkovConditionalPositiveFrozen` is a theorem.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric ProbabilityTheory

universe u

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The variance of a pairing of the whole-plane GFF with a test function is `G(ρ, ρ)`. -/
theorem IsWholePlaneGFF.variance_pairing (hh : IsWholePlaneGFF P hC hcirc) {ρ : ℂ → ℝ}
    (hρ : IsTestFunction univ ρ) :
    Var[fun s => hC s ρ; P] = wholePlaneGFFCov (.pairing ρ) (.pairing ρ) := by
  rw [← covariance_self (hh.measurable_pairing ρ hρ).aemeasurable]
  simpa only [GFFObservable.eval] using hh.covariance_eq (.pairing ρ) (.pairing ρ) hρ hρ

/-- The covariance of two pairings of the whole-plane GFF with test functions is `G(ρ, ρ')`. -/
theorem IsWholePlaneGFF.covariance_pairing (hh : IsWholePlaneGFF P hC hcirc) {ρ ρ' : ℂ → ℝ}
    (hρ : IsTestFunction univ ρ) (hρ' : IsTestFunction univ ρ') :
    cov[fun s => hC s ρ, fun s => hC s ρ'; P] = wholePlaneGFFCov (.pairing ρ) (.pairing ρ') := by
  simpa only [GFFObservable.eval] using hh.covariance_eq (.pairing ρ) (.pairing ρ') hρ hρ'

/-- **Bessel's bound for the covariance potentials.** For pairwise uncorrelated mean-zero test functions `ρ_k`
supported outside `closure W` and a compact `K ⊆ W`, the sums `∑_{k < n} G(ρ_k, ρ_k)⁻¹ (G ρ_k)(x)²` are bounded
uniformly in `n` and `x ∈ K`: they are the Bessel sums of a circle average `h_ε(x)` against the pairings `(h, ρ_k)`. -/
theorem IsWholePlaneGFF.exists_sum_inv_cov_mul_outerPotential_sq_le (hh : IsWholePlaneGFF P hC hcirc)
    {K W : Set ℂ} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) {ρ : ℕ → ℂ → ℝ}
    (hρ : ∀ k, IsTestFunction (closure W)ᶜ (ρ k)) (h0 : ∀ k, ∫ y, ρ k y = 0)
    (horth : ∀ k l, k ≠ l → wholePlaneGFFCov (.pairing (ρ k)) (.pairing (ρ l)) = 0) :
    ∃ M : ℝ, ∀ n, ∀ x ∈ K, ∑ k ∈ Finset.range n,
      (wholePlaneGFFCov (.pairing (ρ k)) (.pairing (ρ k)))⁻¹ * outerPotential (ρ k) x ^ 2 ≤ M := by
  have := hh.isProbabilityMeasure
  obtain ⟨ε, M, hε, hprobe⟩ := hh.exists_circle_probe_of_isCompact hK hW hKW
  refine ⟨M, fun n x hx => ?_⟩
  obtain ⟨-, hvar, hcov⟩ := hprobe x hx
  have hρu : ∀ k, IsTestFunction univ (ρ k) := fun k => (hρ k).mono_set (subset_univ _)
  have hB := LatticeProb.sum_inv_variance_mul_covariance_sq_le_variance (s := Finset.range n)
    (hh.hasGaussianLaw_circle hε x).memLp_two (η := fun k s => hC s (ρ k))
    (fun k _ => hh.memLp_two_pairing (hρu k))
    (fun k _ l _ hkl => (hh.covariance_pairing (hρu k) (hρu l)).trans (horth k l hkl))
  calc _ = ∑ k ∈ Finset.range n, (Var[fun s => hC s (ρ k); P])⁻¹ *
          cov[fun s => hcirc s ε x, fun s => hC s (ρ k); P] ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hh.variance_pairing (hρu k), hcov (ρ k) (hρ k) (h0 k)]
    _ ≤ _ := hB
    _ ≤ M := hvar

/-- **Null intersections of inner and orthogonal outer events.** Let `closure O ⊆ B(c, r)`, let `ψ_n` be test
functions on `O`, and let `ρ_k` be pairwise uncorrelated mean-zero test functions on `(closure B(c, r))ᶜ`. If the
events `{((h, ψ_n))_n ∈ S}` and `{((h, ρ_k))_k ∈ T}` have a null intersection, then one of them is null. -/
theorem IsWholePlaneGFF.measure_inter_eq_zero_or_of_ball (hh : IsWholePlaneGFF P hC hcirc) {O : Set ℂ} {c : ℂ}
    {r : ℝ} (hO : closure O ⊆ ball c r) (ψ ρ : ℕ → ℂ → ℝ) (S T : Set (ℕ → ℝ))
    (hψ : ∀ n, IsTestFunction O (ψ n)) (hρ : ∀ k, IsTestFunction (closure (ball c r))ᶜ (ρ k) ∧ ∫ x, ρ k x = 0)
    (horth : ∀ k l, k ≠ l → wholePlaneGFFCov (.pairing (ρ k)) (.pairing (ρ l)) = 0)
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h0 : P ({ω | (fun n => hC ω (ψ n)) ∈ S} ∩ {ω | (fun k => hC ω (ρ k)) ∈ T}) = 0) :
    P {ω | (fun n => hC ω (ψ n)) ∈ S} = 0 ∨ P {ω | (fun k => hC ω (ρ k)) ∈ T} = 0 := by
  have := hh.isProbabilityMeasure
  obtain ⟨χ, hχ, hχ0, hχ1, hχO⟩ := exists_cutoff_of_closure_subset_ball hO
  have hχu : IsTestFunction univ χ := hχ.mono_set (subset_univ _)
  have hρu : ∀ k, IsTestFunction univ (ρ k) := fun k => (hρ k).1.mono_set (subset_univ _)
  have hψu : ∀ n, IsTestFunction univ (ψ n) := fun n => (hψ n).mono_set (subset_univ _)
  let ι := {φ : ℂ → ℝ // IsTestFunction univ φ}
  let Z : ι → Ω → ℝ := fun φ s => hC s φ.1
  let x : ℕ → ι := fun n => ⟨ψ n, hψu n⟩
  let e : ℕ → ι := fun k => ⟨ρ k, hρu k⟩
  let d : ℕ → ι := fun k => ⟨dualTest χ (ρ k), isTestFunction_dualTest hχu (hρu k) (hρ k).2⟩
  have hZ : IsGaussianProcess Z P := hh.isGaussianProcess_pairing
  have hZm : ∀ t, Measurable (Z t) := fun t => hh.measurable_pairing t.1 t.2
  have hcen : ∀ t, P[Z t] = 0 := fun t => by
    simpa only [GFFObservable.eval] using hh.integral_eq_zero (.pairing t.1) t.2
  have horth' : ∀ k l, k ≠ l → cov[Z (e k), Z (e l); P] = 0 := fun k l hkl =>
    (hh.covariance_pairing (hρu k) (hρu l)).trans (horth k l hkl)
  have hde : ∀ k l, cov[Z (d k), Z (e l); P] = 0 := fun k l =>
    hh.covariance_dualTest_outer hχu hχ1 (hρu k) (hρ k).2 (hρu l) (hρ l).2
      (eq_zero_of_isTestFunction_compl_closure hχ (hρ l).1)
  have hdual : ∀ i k, cov[Z (x i), Z (d k); P] = cov[Z (x i), Z (e k); P] := fun i k =>
    hh.covariance_inner_dualTest hχu hχ1 (hρu k) (hρ k).2 (hψu i)
      (eq_one_of_isTestFunction_of_eqOn (hψ i) hχO)
  obtain ⟨M, hM⟩ := hh.exists_sum_inv_cov_mul_outerPotential_sq_le (K := tsupport χ) (W := ball c r)
    hχ.2.1.isCompact isOpen_ball hχ.2.2 (fun k => (hρ k).1) (fun k => (hρ k).2) horth
  have hsum : Summable fun k => (Var[Z (e k); P])⁻¹ * Var[Z (d k); P] := by
    have h := summable_weight_mul_wholePlaneGFFCov_laplacian_dualElement (M := M) hρu (fun k => (hρ k).2) hχu
      hχ0 hχ1 (fun k y hy => by
        by_contra hρy
        exact hy (eq_zero_of_isTestFunction_compl_closure hχ (hρ k).1 y hρy))
      (fun k => inv_nonneg.mpr (hh.wholePlaneGFFCov_pairing_self_nonneg (hρu k))) hM
    refine h.congr fun k => ?_
    simp only [Z, e, d]
    rw [hh.variance_pairing (hρu k), hh.variance_pairing (isTestFunction_dualTest hχu (hρu k) (hρ k).2)]
    rfl
  exact LatticeProb.Gauss.measure_inter_eq_zero_of_dual_family hZ hZm hcen x e d horth' hde hdual hsum hS hT h0

/-- **Domain Markov property, positivity form**: the input `DomainMarkovConditionalPositiveFrozen` is a theorem. -/
theorem domainMarkovConditionalPositive_holds : DomainMarkovConditionalPositiveFrozen.{u} := by
  intro α₀ Ω _ P _ hC hcirc hh W O hW _ hOW A hA hPA
  obtain ⟨c, r, -, rfl⟩ := hW
  exact hh.ae_condExp_indicator_pos_of_orthogonal_core α₀
    (fun ψ ρ S T hψ hρ horth hS hT h0 => hh.measure_inter_eq_zero_or_of_ball hOW ψ ρ S T hψ hρ horth hS hT h0)
    hA hPA

end HarmonicBalls

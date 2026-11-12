import HarmonicBalls.FirstPass.Phase2.DomainMarkovDualElement
import HarmonicBalls.FirstPass.Phase2.DomainMarkovGramSchmidt
import HarmonicBalls.FirstPass.Phase2.CameronMartinLipschitzShiftDerived

/-!
# The dual family of the outer coordinates of the whole-plane GFF

For a disk `W = B(c, r)` and an open `O` with `closure O ⊆ W` we choose a smooth cutoff `χ` (a test function on `W`
with `0 ≤ χ ≤ 1` and `χ = 1` on `O`). For a mean-zero test function `ρ` let `v = outerPotential ρ` and
`φ_ρ = dualElement χ v (dualConstant χ v)`; the *dual test function* is `Δφ_ρ` (`dualTest χ ρ`). Then:

* `(h, Δφ_ρ)` is uncorrelated with every mean-zero pairing `(h, ρ')` with `χ = 0` on the support of `ρ'`
  (`IsWholePlaneGFF.covariance_dualTest_outer`), in particular with every outer pairing, `tsupport ρ' ⊆ (closure W)ᶜ`;
* `Cov((h, ψ), (h, Δφ_ρ)) = Cov((h, ψ), (h, ρ))` for every test function `ψ` with `χ = 1` on its support
  (`IsWholePlaneGFF.covariance_inner_dualTest`), in particular for every inner test function, `tsupport ψ ⊆ O`.

These are the duality hypotheses of the abstract Gaussian equivalence criterion for the inner field given the outer
field modulo constants. We also record that the pairings with test functions form a Gaussian process.
-/

open MeasureTheory ProbabilityTheory Set Metric Laplacian
open scoped ContDiff

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- A smooth cutoff for `closure O ⊆ B(c, r)`: a test function on the disk with values in `[0, 1]`, equal to `1`
on `O`. -/
theorem exists_cutoff_of_closure_subset_ball {O : Set ℂ} {c : ℂ} {r : ℝ} (hO : closure O ⊆ ball c r) :
    ∃ χ : ℂ → ℝ, IsTestFunction (ball c r) χ ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧ ∀ x ∈ O, χ x = 1 := by
  obtain ⟨r', hr'r, hOr'⟩ := exists_lt_subset_ball isClosed_closure hO
  by_cases hr : 0 < r
  · have h3 : max r' (r / 3) < r := max_lt hr'r (by linarith)
    let b : ContDiffBump c :=
      { rIn := max r' (r / 3)
        rOut := (max r' (r / 3) + r) / 2
        rIn_pos := lt_max_of_lt_right (by positivity)
        rIn_lt_rOut := by linarith }
    refine ⟨b, ⟨b.contDiff, b.hasCompactSupport, ?_⟩, fun x => b.nonneg, fun x => b.le_one, fun x hx => ?_⟩
    · rw [b.tsupport_eq]
      exact closedBall_subset_ball (show (max r' (r / 3) + r) / 2 < r by linarith)
    · refine b.one_of_mem_closedBall ?_
      exact closedBall_subset_closedBall (le_max_left r' (r / 3))
        (ball_subset_closedBall (hOr' (subset_closure hx)))
  · refine ⟨fun _ => 0, isTestFunction_fun_zero _, fun _ => le_rfl, fun _ => zero_le_one, fun x hx => ?_⟩
    exact absurd (pos_of_mem_ball (hO (subset_closure hx))) hr

/-- A cutoff equal to `1` on `O` is `1` on the support of every test function on `O`. -/
theorem eq_one_of_isTestFunction_of_eqOn {χ ψ : ℂ → ℝ} {O : Set ℂ} (hψ : IsTestFunction O ψ)
    (hχ : ∀ x ∈ O, χ x = 1) : ∀ x, ψ x ≠ 0 → χ x = 1 :=
  fun x hx => hχ x (hψ.2.2 (subset_tsupport ψ hx))

/-- A test function on `W` vanishes on the support of every test function on `(closure W)ᶜ`. -/
theorem eq_zero_of_isTestFunction_compl_closure {χ ρ : ℂ → ℝ} {W : Set ℂ} (hχ : IsTestFunction W χ)
    (hρ : IsTestFunction (closure W)ᶜ ρ) : ∀ x, ρ x ≠ 0 → χ x = 0 := by
  intro x hx
  by_contra hχx
  exact hρ.2.2 (subset_tsupport ρ hx) (subset_closure (hχ.2.2 (subset_tsupport χ hχx)))

/-- The dual test function `Δφ_ρ`, `φ_ρ = dualElement χ v (dualConstant χ v)`, `v = outerPotential ρ`. -/
noncomputable def dualTest (χ ρ : ℂ → ℝ) : ℂ → ℝ :=
  Δ (dualElement χ (outerPotential ρ) (dualConstant χ (outerPotential ρ)))

theorem isTestFunction_dualTest {χ ρ : ℂ → ℝ} (hχ : IsTestFunction univ χ) (hρ : IsTestFunction univ ρ)
    (h0 : ∫ x, ρ x = 0) : IsTestFunction univ (dualTest χ ρ) := by
  have h := isTestFunction_dualElement hχ (contDiff_outerPotential_of_integral_eq_zero hρ h0)
    (dualConstant χ (outerPotential ρ))
  exact isTestFunction_laplacian_of_smooth h.1 h.2.1

theorem dualConstant_outerPotential_mul_eq {χ ρ : ℂ → ℝ} (hχ : IsTestFunction univ χ) (hχ1 : ∀ x, χ x ≤ 1)
    (hρ : IsTestFunction univ ρ) (h0 : ∫ x, ρ x = 0) :
    dualConstant χ (outerPotential ρ) * (1 - Real.circleAverage χ 0 1) =
      Real.circleAverage (fun x => χ x * outerPotential ρ x) 0 1 :=
  dualConstant_mul_eq hχ.1.continuous hχ1 (contDiff_outerPotential_of_integral_eq_zero hρ h0).continuous
    (circleAverage_outerPotential_unitCircle hρ)

/-- The dual pairing `(h, Δφ_ρ)` is uncorrelated with every mean-zero pairing `(h, ρ')` supported where `χ = 0`. -/
theorem IsWholePlaneGFF.covariance_dualTest_outer (hh : IsWholePlaneGFF P hC hcirc) {χ ρ ρ' : ℂ → ℝ}
    (hχ : IsTestFunction univ χ) (hχ1 : ∀ x, χ x ≤ 1) (hρ : IsTestFunction univ ρ) (h0 : ∫ x, ρ x = 0)
    (hρ' : IsTestFunction univ ρ') (h0' : ∫ x, ρ' x = 0) (hρ'χ : ∀ x, ρ' x ≠ 0 → χ x = 0) :
    cov[fun s => hC s (dualTest χ ρ), fun s => hC s ρ'; P] = 0 := by
  rw [covariance_comm]
  exact hh.covariance_pairing_laplacian_dualElement_of_eq_zero hρ' hχ
    (contDiff_outerPotential_of_integral_eq_zero hρ h0) (dualConstant_outerPotential_mul_eq hχ hχ1 hρ h0)
    hρ'χ h0'

/-- Duality: `Cov((h, ψ), (h, Δφ_ρ)) = Cov((h, ψ), (h, ρ))` for every test function `ψ` with `χ = 1` on its
support. -/
theorem IsWholePlaneGFF.covariance_inner_dualTest (hh : IsWholePlaneGFF P hC hcirc) {χ ρ ψ : ℂ → ℝ}
    (hχ : IsTestFunction univ χ) (hχ1 : ∀ x, χ x ≤ 1) (hρ : IsTestFunction univ ρ) (h0 : ∫ x, ρ x = 0)
    (hψ : IsTestFunction univ ψ) (hψχ : ∀ x, ψ x ≠ 0 → χ x = 1) :
    cov[fun s => hC s ψ, fun s => hC s (dualTest χ ρ); P] = cov[fun s => hC s ψ, fun s => hC s ρ; P] := by
  rw [hh.covariance_pairing_eq_integral_outerPotential hψ hρ]
  exact hh.covariance_pairing_laplacian_dualElement_of_eq_one hψ hχ
    (contDiff_outerPotential_of_integral_eq_zero hρ h0) (dualConstant_outerPotential_mul_eq hχ hχ1 hρ h0) hψχ

/-- The pairings of the whole-plane GFF with test functions form a Gaussian process. -/
theorem IsWholePlaneGFF.isGaussianProcess_pairing (hh : IsWholePlaneGFF P hC hcirc) :
    IsGaussianProcess (fun (ψ : {ψ : ℂ → ℝ // IsTestFunction univ ψ}) s => hC s ψ.1) P :=
  hh.isGaussianProcess.comp_right
    (fun ψ : {ψ : ℂ → ℝ // IsTestFunction univ ψ} => (⟨.pairing ψ.1, ψ.2⟩ : GFFObservable.Admissible))

end HarmonicBalls

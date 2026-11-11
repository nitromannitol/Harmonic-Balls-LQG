import HarmonicBalls.Proofs.Sec8.ContinuousLocalVersions
import HarmonicBalls.Proofs.Sec3.PositiveDistribution

/-! # Local field sigma algebras after centering

A test function of integral one gives a measurable representative of the
field modulo additive constants on a smaller open set.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric

/-- Every nonempty open set admits a unit-integral reference test function. -/
theorem IsTestFunction.exists_integral_eq_one {U : Set ℂ}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ψ : ℂ → ℝ, IsTestFunction U ψ ∧ ∫ x, ψ x = 1 := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  let b : ContDiffBump z := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, ?_⟩,
    b.integral_normed⟩
  change closure (Function.support (b.normed volume)) ⊆ U
  rw [b.support_normed_eq, closure_ball _ (by positivity : (r / 2) ≠ 0)]
  exact (Metric.closedBall_subset_ball (by linarith)).trans hrU

/-- Center each test function against a reference test function. This formula
is defined for arbitrary pairing functions, without assuming linearity. -/
noncomputable def centeredTestPairing (T : (ℂ → ℝ) → ℝ) (ψ : ℂ → ℝ)
    (φ : ℂ → ℝ) : ℝ :=
  T (fun x => 1 * φ x + (-(∫ y, φ y)) * ψ x)

/-- Local pairings of the centered field are measurable from the larger
field modulo constants, provided the reference test has integral one. -/
theorem fieldSigmaAlgebra_centeredTestPairing_le_modConst
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) {U V : Set ℂ}
    (hUV : U ⊆ V) (ψ : ℂ → ℝ) (hψ : IsTestFunction V ψ)
    (hψint : ∫ x, ψ x = 1) :
    fieldSigmaAlgebra α (fun ω => centeredTestPairing (hC ω) ψ) U ≤
      Section6.fieldSigmaAlgebraModConst α hC V := by
  unfold fieldSigmaAlgebra
  apply iSup_le
  intro φ
  apply iSup_le
  intro hφ
  have hφV : IsTestFunction V φ := hφ.mono_set hUV
  let χ : ℂ → ℝ := fun x => 1 * φ x + (-(∫ y, φ y)) * ψ x
  have hχ : IsTestFunction V χ := hφV.const_mul_add_const_mul hψ 1 _
  have hintφ : Integrable φ := hφV.1.continuous.integrable_of_hasCompactSupport hφV.2.1
  have hintψ : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hχint : ∫ x, χ x = 0 := by
    dsimp [χ]
    rw [integral_add (hintφ.const_mul 1) (hintψ.const_mul _), integral_const_mul,
      integral_const_mul, hψint]
    ring
  have hm := measurable_fieldPairing_modConst α hC V χ ⟨hχ, hχint⟩
  have hm' : Measurable[Section6.fieldSigmaAlgebraModConst α hC V]
      (fun ω => fieldPairing α (centeredTestPairing (hC ω) ψ) φ) := by
    have ht := hm.add_const (α * (∫ x, χ x * Real.log ‖x‖) -
      α * (∫ x, φ x * Real.log ‖x‖))
    convert ht using 1
    ext ω
    simp only [fieldPairing, centeredTestPairing, χ]
    ring
  exact hm'.comap_le

/-- Centering against a unit-integral test generates precisely the local
field sigma algebra modulo additive constants. -/
theorem fieldSigmaAlgebra_centeredTestPairing_eq_modConst
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    fieldSigmaAlgebra α (fun ω => centeredTestPairing (hC ω) ψ) U =
      Section6.fieldSigmaAlgebraModConst α hC U := by
  apply le_antisymm
  · exact fieldSigmaAlgebra_centeredTestPairing_le_modConst α hC Subset.rfl ψ hψ hψint
  · unfold Section6.fieldSigmaAlgebraModConst
    apply iSup_le
    intro φ
    apply iSup_le
    intro hφ
    have heq : (fun ω => fieldPairing α (hC ω) φ) =
        (fun ω => fieldPairing α (centeredTestPairing (hC ω) ψ) φ) := by
      funext ω
      unfold fieldPairing centeredTestPairing
      congr 2
      funext x
      simp only [hφ.2, neg_zero, zero_mul, add_zero, one_mul]
    rw [heq]
    unfold fieldSigmaAlgebra
    exact le_iSup_of_le φ (le_iSup (fun h : IsTestFunction U φ =>
      MeasurableSpace.comap
        (fun ω => fieldPairing α (centeredTestPairing (hC ω) ψ) φ) inferInstance) hφ.1)

/-- On a nonempty open set, the field modulo constants has a centered
pairing representation using a test function supported in that set. -/
theorem exists_centeredTestPairing_fieldSigmaAlgebra_eq_modConst
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) {U : Set ℂ}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ψ : ℂ → ℝ, IsTestFunction U ψ ∧ (∫ x, ψ x = 1) ∧
      fieldSigmaAlgebra α (fun ω => centeredTestPairing (hC ω) ψ) U =
        Section6.fieldSigmaAlgebraModConst α hC U := by
  obtain ⟨ψ, hψ, hint⟩ := IsTestFunction.exists_integral_eq_one hU hne
  exact ⟨ψ, hψ, hint, fieldSigmaAlgebra_centeredTestPairing_eq_modConst α hC U ψ hψ hint⟩

/-- Centered local test pairings are unchanged by adding a constant to the
field, even when the pairing functional is not assumed to be linear. -/
theorem centeredTestPairing_add_const {U : Set ℂ}
    (T : (ℂ → ℝ) → ℝ) (c : ℝ) {ψ φ : ℂ → ℝ}
    (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (hφ : IsTestFunction U φ) :
    centeredTestPairing (addFunPairing T (fun _ => c)) ψ φ = centeredTestPairing T ψ φ := by
  have hintφ : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hintψ : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hzero : ∫ x, (1 * φ x + (-(∫ y, φ y)) * ψ x) = 0 := by
    rw [integral_add (hintφ.const_mul 1) (hintψ.const_mul _), integral_const_mul,
      integral_const_mul, hψint]
    ring
  simp only [centeredTestPairing, addFunPairing, integral_const_mul, hzero, mul_zero, add_zero]

/-- For a linear distribution, centering test functions agrees with subtracting
its reference pairing times the integral of the test function. -/
theorem centeredTestPairing_eq_of_linearOnTests {U : Set ℂ}
    (T : (ℂ → ℝ) → ℝ) (hT : IsLinearOnTests U T)
    {ψ φ : ℂ → ℝ} (hψ : IsTestFunction U ψ) (hφ : IsTestFunction U φ) :
    centeredTestPairing T ψ φ = T φ - (∫ x, φ x) * T ψ := by
  unfold centeredTestPairing
  rw [hT φ ψ hφ hψ 1 (-(∫ x, φ x))]
  ring

/-- If the pairings are linear on test functions, subtracting the reference
pairing realizes the local field modulo additive constants. -/
theorem fieldSigmaAlgebra_sub_reference_eq_modConst
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ)
    (hlin : ∀ ω, IsLinearOnTests U (hC ω)) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    fieldSigmaAlgebra α (fun ω φ => hC ω φ - (∫ x, φ x) * hC ω ψ) U =
      Section6.fieldSigmaAlgebraModConst α hC U := by
  rw [← fieldSigmaAlgebra_centeredTestPairing_eq_modConst α hC U ψ hψ hψint]
  unfold fieldSigmaAlgebra
  congr 1
  ext1 φ
  congr 1
  ext1 hφ
  congr 1
  funext ω
  simp only [fieldPairing, centeredTestPairing_eq_of_linearOnTests (hC ω) (hlin ω) hψ hφ]


end HarmonicBalls

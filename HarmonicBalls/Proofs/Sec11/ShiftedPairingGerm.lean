import HarmonicBalls.Proofs.Sec11.PinchModConstGerm

/-! # Germ triviality after deterministic field shifts

The Section 8 germ proof uses Leonardo Bonanno's LatticeProb formalization.
A comparison of the full local pairing laws remains an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A deterministic shift of all pairing values preserves the full local field
sigma algebra. No regularity of the shift is required. -/
theorem fieldSigmaAlgebra_eq_of_deterministic_pairing_shift
    {Ω : Type*} (α : ℝ) (hC hC' : Ω → (ℂ → ℝ) → ℝ)
    (d : (ℂ → ℝ) → ℝ) (hd : ∀ ω φ, hC' ω φ = hC ω φ + d φ) (U : Set ℂ) :
    fieldSigmaAlgebra α hC' U = fieldSigmaAlgebra α hC U := by
  unfold fieldSigmaAlgebra
  congr 1; ext1 φ; congr 1; ext1 _
  have heq : (fun ω => fieldPairing α (hC' ω) φ) =
      (fun t : ℝ => t + d φ) ∘ fun ω => fieldPairing α (hC ω) φ := by
    funext ω
    simp only [Function.comp_apply, fieldPairing, hd]
    ring
  rw [heq, ← MeasurableSpace.comap_comp]
  congr 1
  exact (MeasurableEquiv.addRight (d φ)).measurableEmbedding.comap_eq

/-- A deterministic shift, including a singular one, leaves the origin germ
of a whole-plane GFF trivial modulo constants. -/
theorem IsWholePlaneGFF.origin_shifted_modConst_germ_trivial
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α : ℝ)
    (d : (ℂ → ℝ) → ℝ) (hd : ∀ ω φ, hC' ω φ = hC ω φ + d φ) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC' (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  intro A hA
  apply h.origin_germ_trivial α A
  intro ε hε
  rw [← fieldSigmaAlgebraModConst_eq_of_deterministic_pairing_shift α hC hC' d hd]
  exact hA ε hε

/-- If the shifted pairing process under `P` is locally absolutely continuous
with respect to its law under the GFF measure `Q`, then its origin germ modulo
constants is `P`-trivial. The deterministic shift may be singular. -/
theorem origin_shifted_modConst_germ_trivial_of_pairing_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hC hcirc) (α : ℝ)
    (d : (ℂ → ℝ) → ℝ) (hd : ∀ ω φ, hC' ω φ = hC ω φ + d φ)
    {r : ℝ} (hr : 0 < r)
    (hAC : P.map (localFieldPairings α hC' (ball 0 r)) ≪
      Q.map (localFieldPairings α hC' (ball 0 r))) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC' (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  have heq (U : Set ℂ) : fieldSigmaAlgebra α hC' U = fieldSigmaAlgebra α hC U :=
    fieldSigmaAlgebra_eq_of_deterministic_pairing_shift α hC hC' d hd U
  have hm : fieldSigmaAlgebra α hC' (ball 0 r) ≤ mΩ := by
    rw [heq]
    exact hQ.fieldSigmaAlgebra_le α _
  have hac' := fieldSigmaAlgebra_trim_absolutelyContinuous_of_pairing_law P Q α hC'
    (ball 0 r) hm hAC
  have hac : P.trim (hQ.fieldSigmaAlgebra_le α (ball 0 r)) ≪
      Q.trim (hQ.fieldSigmaAlgebra_le α (ball 0 r)) := by
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hz
    have hs' : MeasurableSet[fieldSigmaAlgebra α hC' (ball 0 r)] s := by
      rw [heq]
      exact hs
    have hz' : Q.trim hm s = 0 := by
      rw [trim_measurableSet_eq hm hs']
      simpa only [trim_measurableSet_eq _ hs] using hz
    have hp := hac' hz'
    rw [trim_measurableSet_eq hm hs'] at hp
    simpa only [trim_measurableSet_eq _ hs] using hp
  intro A hA
  apply origin_modConst_germ_trivial_of_local_absoluteContinuous P Q hQ α hr hac A
  intro ε hε
  rw [← fieldSigmaAlgebraModConst_eq_of_deterministic_pairing_shift α hC hC' d hd]
  exact hA ε hε


end HarmonicBalls

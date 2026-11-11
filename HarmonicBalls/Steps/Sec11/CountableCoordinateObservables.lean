import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity
import HarmonicBalls.Steps.Sec11.LocalPairingLaw
import Mathlib.MeasureTheory.Constructions.Cylinders

/-! # Almost-sure equality of field observables

An observable of a product measurable space only uses countably many
coordinates for almost-sure equality. The imported Section 8 arguments use
Leonardo Bonanno's LatticeProb formalization of the ergodic theorem.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter

/-- A measurable observable into a countably separated space preserves
coordinatewise almost-sure equality, even for an uncountable index type. -/
theorem ae_eq_measurable_comp_of_coordinatewise_ae_eq
    {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace.CountablySeparated E] {P : Measure Ω}
    {A : ι → Type*} [∀ i, MeasurableSpace (A i)]
    (X Y : Ω → ∀ i, A i) (hXY : ∀ i, ∀ᵐ ω ∂P, X ω i = Y ω i)
    (F : (∀ i, A i) → E) (hF : Measurable F) :
    ∀ᵐ ω ∂P, F (X ω) = F (Y ω) := by
  obtain ⟨e, he, hinj⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated E
  have hn (n : ℕ) : ∀ᵐ ω ∂P, e (F (X ω)) n = e (F (Y ω)) n := by
    let s : Set (∀ i, A i) := {v | e (F v) n = true}
    have hs : MeasurableSet s :=
      ((measurable_pi_apply n).comp (he.comp hF)) (MeasurableSet.singleton true)
    obtain ⟨I, t, hI, hst⟩ := hs.eq_preimage_restrict_countable
    let : Countable I := hI.to_subtype
    have hcoord : ∀ᵐ ω ∂P, ∀ i : I, X ω i.1 = Y ω i.1 :=
      ae_all_iff.mpr (fun i => hXY i.1)
    filter_upwards [hcoord] with ω hcoord
    have hr : I.domRestrict (X ω) = I.domRestrict (Y ω) := by
      funext i
      exact hcoord i
    have hi : X ω ∈ s ↔ Y ω ∈ s := by
      rw [hst]
      change I.domRestrict (X ω) ∈ t ↔ I.domRestrict (Y ω) ∈ t
      rw [hr]
    change (e (F (X ω)) n = true) ↔ (e (F (Y ω)) n = true) at hi
    cases hx : e (F (X ω)) n <;> cases hy : e (F (Y ω)) n <;> simp_all
  have hall : ∀ᵐ ω ∂P, ∀ n, e (F (X ω)) n = e (F (Y ω)) n := ae_all_iff.mpr hn
  filter_upwards [hall] with ω hω
  apply hinj
  funext n
  exact hω n

/-- Every standard Borel observable of the reference-shifted local field has
an almost-sure version measurable in the field modulo constants. -/
theorem IsWholePlaneGFF.exists_modConst_observable_of_reference_shift
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] {P : Measure Ω} {α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {U : Set ℂ}
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (f : Ω → E)
    (hf : Measurable[fieldSigmaAlgebra α
      (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U] f) :
    ∃ g : Ω → E,
      Measurable[Section6.fieldSigmaAlgebraModConst α hC U] g ∧
      ∀ᵐ ω ∂P, g ω = f ω := by
  let X := localFieldPairings α
    (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U
  let Y := localFieldPairings α (fun ω => centeredTestPairing (hC ω) ψ) U
  have hXY (φ : LocalFieldTest U) : ∀ᵐ ω ∂P, X ω φ = Y ω φ := by
    filter_upwards [h.ae_centeredTestPairing_eq φ.2 hψ] with ω hω
    dsimp [X, Y, localFieldPairings, fieldPairing, addFunPairing]
    rw [hω, integral_const_mul]
    ring
  have hY : Measurable[Section6.fieldSigmaAlgebraModConst α hC U] Y := by
    rw [← fieldSigmaAlgebra_centeredTestPairing_eq_modConst α hC U ψ hψ hψint,
      fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact comap_measurable Y
  have hf' : Measurable[MeasurableSpace.comap X inferInstance] f := by
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact hf
  obtain ⟨F, hF, hFeq⟩ := hf'.exists_eq_measurable_comp
  refine ⟨F ∘ Y, hF.comp hY, ?_⟩
  have heq := ae_eq_measurable_comp_of_coordinatewise_ae_eq X Y hXY F hF
  filter_upwards [heq] with ω hω
  rw [Function.comp_apply, ← hω, hFeq]
  rfl


end HarmonicBalls

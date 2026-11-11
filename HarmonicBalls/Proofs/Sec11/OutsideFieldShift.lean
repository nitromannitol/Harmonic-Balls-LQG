import HarmonicBalls.Proofs.Sec11.ConditionalPositivityShift
import HarmonicBalls.Steps.Sec11.LocalPairingLaw
import HarmonicBalls.Proofs.Sec11.SingularSmoothShiftPairing

/-! # Outside-field invariance under an interior shift -/

namespace HarmonicBalls
open MeasureTheory Set Filter

/-- Equality of the entire local pairing process implies preservation of every
    event measurable with respect to the local field. -/
theorem ae_fieldSigmaAlgebra_event_iff_of_localPairings_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (τ : Ω → Ω)
    (hpair : ∀ᵐ ω ∂P, localFieldPairings α hC U (τ ω) = localFieldPairings α hC U ω)
    (F : Set Ω) (hF : MeasurableSet[fieldSigmaAlgebra α hC U] F) :
    ∀ᵐ ω ∂P, ω ∈ F ↔ τ ω ∈ F := by
  rw [fieldSigmaAlgebra_eq_comap_localFieldPairings] at hF
  obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hF
  filter_upwards [hpair] with ω hω
  change localFieldPairings α hC U ω ∈ S ↔ localFieldPairings α hC U (τ ω) ∈ S
  rw [hω]

/-- A shift that vanishes on the observed region leaves all local pairing
    observables, and hence all local-field events, unchanged almost surely. -/
theorem ae_fieldSigmaAlgebra_event_iff_of_interior_shift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (τ : Ω → Ω)
    (g : ℂ → ℝ) (hg : ∀ z ∈ U, g z = 0)
    (hshift : ∀ᵐ ω ∂P, hC (τ ω) = addFunPairing (hC ω) g)
    (F : Set Ω) (hF : MeasurableSet[fieldSigmaAlgebra α hC U] F) :
    ∀ᵐ ω ∂P, ω ∈ F ↔ τ ω ∈ F := by
  apply ae_fieldSigmaAlgebra_event_iff_of_localPairings_eq P α hC U τ _ F hF
  filter_upwards [hshift] with ω hω
  funext φ
  have hzero : (fun z => g z * φ.1 z) = 0 := by
    funext z
    by_cases hz : z ∈ U
    · simp [hg z hz]
    · have hφ : φ.1 z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hz' => hz (φ.2.2.2 hz'))
      simp [hφ]
  simp [localFieldPairings, fieldPairing, hω, addFunPairing, hzero]

/-- A conditionally positive seed transfers through a shift supported away
    from the region generating the conditioning field σ-algebra. -/
theorem condExp_indicator_pos_of_interior_field_shift
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ)
    (hm : fieldSigmaAlgebra α hC U ≤ m₀) {B H : Set Ω}
    (hB : MeasurableSet B) (hH : MeasurableSet H)
    (τ : Ω → Ω) (hτ : Measurable τ) (hac : P ≪ P.map τ)
    (g : ℂ → ℝ) (hg : ∀ z ∈ U, g z = 0)
    (hshift : ∀ᵐ ω ∂P, hC (τ ω) = addFunPairing (hC ω) g)
    (himage : ∀ᵐ ω ∂P, τ ω ∈ B → ω ∈ H)
    (hseed : ∀ᵐ ω ∂P, 0 <
      (P[B.indicator (fun _ => (1 : ℝ)) | fieldSigmaAlgebra α hC U]) ω) :
    ∀ᵐ ω ∂P, 0 <
      (P[H.indicator (fun _ => (1 : ℝ)) | fieldSigmaAlgebra α hC U]) ω := by
  apply condExp_indicator_pos_of_outside_preserving_shift P (fieldSigmaAlgebra α hC U)
    hm hB hH τ hτ hac _ himage hseed
  intro F hF
  exact ae_fieldSigmaAlgebra_event_iff_of_interior_shift P α hC U τ g hg hshift F hF

end HarmonicBalls

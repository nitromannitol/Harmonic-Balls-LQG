import HarmonicBalls.Proofs.Sec11.MassDiameterFullSupportShift

/-! # Mass amplification on a prescribed event -/

namespace HarmonicBalls
open MeasureTheory Set
open scoped ENNReal

/-- Full support permits mass amplification while retaining a prescribed
    measurable positive-probability event. -/
theorem exists_mass_increasing_shift_preserving_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (A : Set Ω) (hA : MeasurableSet A) {S U O : Set ℂ} (hAp : 0 < P A)
    (hScompact : IsCompact S) (hS : MeasurableSet S)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hO : IsOpen O) (hSO : S ⊆ O)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    {γ M : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ z, 0 ≤ f z) ∧
      (∀ z ∉ O, f z = 0) ∧
      0 < P {ω | ω ∈ A ∧ ENNReal.ofReal M <
        (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S} := by
  have hp : 0 < (P.restrict A) univ := by simpa using hAp
  obtain ⟨f, hf, hnonneg, hout, hpos⟩ :=
    exists_mass_increasing_shift_of_ae_full_support (P.restrict A) μ univ hp
      hScompact hS hU hUne hUS hO hSO (ae_restrict_of_ae hfull) hγ hM
  refine ⟨f, hf, hnonneg, hout, ?_⟩
  rw [Measure.restrict_apply' hA] at hpos
  have heq : {ω | ω ∈ A ∧ ENNReal.ofReal M <
      (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S} =
      {ω | ENNReal.ofReal M <
        (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S} ∩ A := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, and_comm]
  rw [heq]
  exact hpos

end HarmonicBalls

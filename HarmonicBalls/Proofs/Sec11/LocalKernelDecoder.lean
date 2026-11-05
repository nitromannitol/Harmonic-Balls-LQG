import HarmonicBalls.Proofs.Sec8.GermConditionalKernel

/-! # Measure decoders from local scalar observations

A conditional kernel on the observation space reconstructs a random
probability measure from its countable scalar observations. The imported
Section 8 development uses Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace HarmonicBalls

/-- A random probability kernel whose masses on a generating π-system factor
through an observation admits a measure-valued decoder on that observation. -/
theorem exists_measure_decoder_of_piSystem
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : Measurable X)
    (κ : Kernel Ω ℂ) [IsMarkovKernel κ]
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V) (huniv : univ ∈ S)
    (F : S → E → ℝ≥0∞) (hF : ∀ V, Measurable (F V))
    (hversion : ∀ V : S, ∀ᵐ ω ∂P, κ ω V.1 = F V (X ω)) :
    ∃ D : E → Measure ℂ, Measurable D ∧ (∀ v, IsProbabilityMeasure (D v)) ∧
      ∀ᵐ ω ∂P, D (X ω) = κ ω := by
  let f : Ω × ℂ → E × ℂ := fun p => (X p.1, p.2)
  have hf : Measurable f := (hX.comp measurable_fst).prodMk measurable_snd
  let J : Measure (E × ℂ) := (P ⊗ₘ κ).map f
  have : IsFiniteMeasure J := Measure.isFiniteMeasure_map (P ⊗ₘ κ) f
  have hfst : J.fst = P.map X := by
    apply Measure.ext
    intro A hA
    rw [Measure.fst_apply hA, Measure.map_apply hf (measurable_fst hA),
      Measure.map_apply hX hA]
    have hpre : f ⁻¹' (Prod.fst ⁻¹' A) = (X ⁻¹' A) ×ˢ univ := by
      ext p
      simp [f]
    rw [hpre, Measure.compProd_apply_prod (hX hA) MeasurableSet.univ]
    simp
  have heq (V : S) : ∀ᵐ ω ∂P, J.condKernel (X ω) V.1 = κ ω V.1 := by
    have hV := hsets V.1 V.2
    have heq' : (fun v => J.condKernel v V.1) =ᵐ[P.map X] F V := by
      apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (J.condKernel.measurable_coe hV) (hF V)
      intro A hA _
      calc
        ∫⁻ v in A, J.condKernel v V.1 ∂(P.map X) = J (A ×ˢ V.1) := by
          rw [← hfst]
          exact Measure.setLIntegral_condKernel_eq_measure_prod hA hV
        _ = (P ⊗ₘ κ) ((X ⁻¹' A) ×ˢ V.1) := by
          rw [Measure.map_apply hf (hA.prod hV)]
          rfl
        _ = ∫⁻ ω in X ⁻¹' A, κ ω V.1 ∂P :=
          Measure.compProd_apply_prod (hX hA) hV
        _ = ∫⁻ ω in X ⁻¹' A, F V (X ω) ∂P :=
          lintegral_congr_ae (ae_restrict_of_ae (hversion V))
        _ = ∫⁻ v in A, F V v ∂(P.map X) :=
          (setLIntegral_map hA (hF V) hX).symm
    have hm : MeasurableSet {v | J.condKernel v V.1 = F V v} :=
      measurableSet_eq_fun (J.condKernel.measurable_coe hV) (hF V)
    filter_upwards [(ae_map_iff hX.aemeasurable hm).1 heq', hversion V] with ω h1 h2
    exact h1.trans h2.symm
  let : Countable S := hcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ V ∈ S, J.condKernel (X ω) V = κ ω V := by
    filter_upwards [ae_all_iff.mpr heq] with ω hω V hV
    exact hω ⟨V, hV⟩
  refine ⟨fun v => J.condKernel v, ?_, ?_, ?_⟩
  · exact Measurable.measure_of_isPiSystem hgen hpi
      (fun V hV => J.condKernel.measurable_coe (hsets V hV))
      (J.condKernel.measurable_coe MeasurableSet.univ)
  · intro v
    infer_instance
  · filter_upwards [hall] with ω hω
    exact ext_of_generate_finite S hgen hpi hω (hω univ huniv)

#print axioms exists_measure_decoder_of_piSystem

end HarmonicBalls

import HarmonicBalls.Proofs.Sec2.MixtureGFF

/-! # Pulling back a whole-plane GFF

A measure-preserving change of probability space preserves the whole-plane GFF
structure. This permits fields on different spaces to be placed on a common
product space before applying the GFF mixture theorem.
-/

namespace HarmonicBalls
open MeasureTheory ProbabilityTheory

/-- A whole-plane GFF remains one after a measure-preserving pullback. -/
theorem IsWholePlaneGFF.comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {f : Ω' → Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hf : MeasurePreserving f P' P) :
    IsWholePlaneGFF P' (hC ∘ f) (hcirc ∘ f) := by
  have hm : ∀ o : GFFObservable.Admissible,
      Measurable fun ω => o.1.eval (hC ω) (hcirc ω) := by
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact h.measurable_pairing φ ho
    | circle r z => exact h.measurable_circle r z ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ hφ
    exact (h.measurable_pairing φ hφ).comp hf.measurable
  · intro r z hr
    exact (h.measurable_circle r z hr).comp hf.measurable
  · refine ⟨fun I => ?_⟩
    have hI : Measurable (fun ω => I.restrict fun o => o.1.eval (hC ω) (hcirc ω)) :=
      measurable_pi_iff.mpr fun i => hm i.1
    refine ⟨(hI.comp hf.measurable).aemeasurable, ?_⟩
    change IsGaussian (P'.map ((fun ω => I.restrict fun o =>
      o.1.eval (hC ω) (hcirc ω)) ∘ f))
    rw [← Measure.map_map hI hf.measurable, hf.map_eq]
    exact (h.isGaussianProcess.hasGaussianLaw I).isGaussian_map
  · intro o ho
    have hmeas : AEStronglyMeasurable (fun ω => o.eval (hC ω) (hcirc ω)) P :=
      (hm ⟨o, ho⟩).aestronglyMeasurable
    have heq := integral_map hf.measurable.aemeasurable (hf.map_eq ▸ hmeas)
    rw [hf.map_eq] at heq
    exact heq.symm.trans (h.integral_eq_zero o ho)
  · intro o o' ho ho'
    have hmeas : AEStronglyMeasurable (fun ω => o.eval (hC ω) (hcirc ω)) P :=
      (hm ⟨o, ho⟩).aestronglyMeasurable
    have hmeas' : AEStronglyMeasurable (fun ω => o'.eval (hC ω) (hcirc ω)) P :=
      (hm ⟨o', ho'⟩).aestronglyMeasurable
    have heq := covariance_map_fun (hf.map_eq ▸ hmeas) (hf.map_eq ▸ hmeas') hf.measurable.aemeasurable
    rw [hf.map_eq] at heq
    exact heq.symm.trans (h.covariance_eq o o' ho ho')
  · exact hf.quasiMeasurePreserving.tendsto_ae h.ae_continuousOn_circle

#print axioms IsWholePlaneGFF.comp_measurePreserving

end HarmonicBalls

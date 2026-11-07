import HarmonicBalls.Proofs.Sec5.GaussianProcessLaw

/-! # Law of the admissible whole-plane GFF observations

The finite-dimensional Gaussian law used here is established in
`GaussianProcessLaw`; the project also builds on Leonardo Bonanno's GFF
formalization. The product measurable space records all admissible observations.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory

/-- The admissible observation process is measurable for the product sigma algebra. -/
theorem IsWholePlaneGFF.measurable_admissibleObservationProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) :
    Measurable (fun (ω : Ω) (o : GFFObservable.Admissible) =>
      o.1.eval (hC ω) (hcirc ω)) := by
  apply measurable_pi_iff.mpr
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ => exact h.measurable_pairing φ ho
  | circle r z => exact h.measurable_circle r z ho

/-- The entire admissible observation process has the same law for any two
whole-plane GFF realizations, even on different probability spaces. -/
theorem IsWholePlaneGFF.map_admissibleObservationProcess_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc') :
    P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
      P'.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC' ω) (hcirc' ω)) := by
  let _ := h.isGaussianProcess.isProbabilityMeasure
  let _ := h'.isGaussianProcess.isProbabilityMeasure
  apply (isProjectiveLimit_map h.measurable_admissibleObservationProcess.aemeasurable).unique
  intro I
  rw [isProjectiveLimit_map h'.measurable_admissibleObservationProcess.aemeasurable I]
  exact (h.identDistrib_finite_observables h' Subtype.val).map_eq.symm

#print axioms IsWholePlaneGFF.measurable_admissibleObservationProcess
#print axioms IsWholePlaneGFF.map_admissibleObservationProcess_eq

end HarmonicBalls

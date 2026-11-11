import HarmonicBalls.Proofs.Sec11.LQGJointFieldIntegralLaw
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Joint laws of LQG open masses and field observables -/

namespace HarmonicBalls

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

/-- Countably many open-set LQG masses and a common measurable countable
field observable have the same joint law for any two whole-plane GFFs. -/
theorem IsWholePlaneGFF.identDistrib_lqg_open_masses_with_observable
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Countable ι]
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (F : (GFFObservable.Admissible → ℝ) → ℕ → ℝ) (hF : Measurable F) :
    IdentDistrib
      (fun ω => ((fun i => μ ω (U i)), F (fun o => o.1.eval (hC ω) (hcirc ω))))
      (fun ω => ((fun i => μ' ω (U i)), F (fun o => o.1.eval (hC' ω) (hcirc' ω)))) P P' := by
  classical
  choose f hf hfc hmass using fun i => exists_open_mass_test_functions (hU i)
  let G : ((ι × ℕ → ℝ) × (ℕ → ℝ)) → (ι → ℝ≥0∞) × (ℕ → ℝ) :=
    fun x => (fun i => ⨆ n, ENNReal.ofReal (x.1 (i, n)), x.2)
  have hG : Measurable G := by
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro i
      exact Measurable.iSup fun n => ((measurable_pi_apply (i, n)).comp measurable_fst).ennreal_ofReal
    · exact measurable_snd
  have hd := (h.identDistrib_lqg_integrals_with_observable h' hμ hμ'
    (f := fun p : ι × ℕ => f p.1 p.2) (fun p => hf p.1 p.2)
    (fun p => hfc p.1 p.2) F hF).comp hG
  have heq : ∀ᵐ ω ∂P, G ((fun p : ι × ℕ => ∫ z, f p.1 p.2 z ∂(μ ω)),
      F (fun o => o.1.eval (hC ω) (hcirc ω))) =
      ((fun i => μ ω (U i)), F (fun o => o.1.eval (hC ω) (hcirc ω))) := by
    filter_upwards [hμ] with ω hω
    apply Prod.ext
    · funext i
      exact (hmass i (μ ω) hω.isLocallyFiniteMeasure).symm
    · rfl
  have heq' : ∀ᵐ ω ∂P', G ((fun p : ι × ℕ => ∫ z, f p.1 p.2 z ∂(μ' ω)),
      F (fun o => o.1.eval (hC' ω) (hcirc' ω))) =
      ((fun i => μ' ω (U i)), F (fun o => o.1.eval (hC' ω) (hcirc' ω))) := by
    filter_upwards [hμ'] with ω hω
    apply Prod.ext
    · funext i
      exact (hmass i (μ' ω) hω.isLocallyFiniteMeasure).symm
    · rfl
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq')


end HarmonicBalls

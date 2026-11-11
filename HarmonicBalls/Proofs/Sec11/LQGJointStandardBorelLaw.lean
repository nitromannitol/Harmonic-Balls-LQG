import HarmonicBalls.Proofs.Sec11.LQGJointFieldMeasureLaw
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-! # Joint law of LQG measure and standard Borel field observations -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory

/-- A measurable standard Borel observation of the complete field and its
LQG measure have a joint law independent of the realization. -/
theorem IsWholePlaneGFF.identDistrib_lqgMeasure_with_standardBorel_observable
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [StandardBorelSpace E]
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (F : (GFFObservable.Admissible → ℝ) → E) (hF : Measurable F) :
    IdentDistrib
      (fun ω => (μ ω, F (fun o => o.1.eval (hC ω) (hcirc ω))))
      (fun ω => (μ' ω, F (fun o => o.1.eval (hC' ω) (hcirc' ω)))) P P' := by
  let e : E → ℝ := embeddingReal E
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal E
  let G : (GFFObservable.Admissible → ℝ) → ℕ → ℝ := fun v _ => e (F v)
  have hG : Measurable G := Measurable.of_eval fun _ => he.measurable.comp hF
  let X : Ω → Measure ℂ × E := fun ω =>
    (μ ω, F (fun o => o.1.eval (hC ω) (hcirc ω)))
  let Y : Ω' → Measure ℂ × E := fun ω =>
    (μ' ω, F (fun o => o.1.eval (hC' ω) (hcirc' ω)))
  have hobs := h.identDistrib_observables_across_spaces h'
  have hXm : AEMeasurable X P := (h.aemeasurable_lqgMeasure hμ).prodMk
    (hF.comp_aemeasurable hobs.aemeasurable_fst)
  have hYm : AEMeasurable Y P' := (h'.aemeasurable_lqgMeasure hμ').prodMk
    (hF.comp_aemeasurable hobs.aemeasurable_snd)
  let e' : Measure ℂ × E → Measure ℂ × ℝ := Prod.map id e
  have he' : MeasurableEmbedding e' := MeasurableEmbedding.id.prodMap he
  have hd := (h.identDistrib_lqgMeasure_with_observable h' hμ hμ' G hG).comp
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  refine ⟨hXm, hYm, he'.map_injective ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable he'.measurable.aemeasurable hXm,
    AEMeasurable.map_map_of_aemeasurable he'.measurable.aemeasurable hYm]
  exact hd.map_eq

/-- A common measurable continuous-distance observable of two fields gives
identical joint laws of their LQG measures and distance observations. -/
theorem IsWholePlaneGFF.identDistrib_lqgMeasure_metric_of_common_observable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    {D : Ω → C(ℂ × ℂ, ℝ)} {D' : Ω' → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (F : (GFFObservable.Admissible → ℝ) → C(ℂ × ℂ, ℝ)) (hF : Measurable F)
    (hD : ∀ᵐ ω ∂P, F (fun o => o.1.eval (hC ω) (hcirc ω)) = D ω)
    (hD' : ∀ᵐ ω ∂P', F (fun o => o.1.eval (hC' ω) (hcirc' ω)) = D' ω) :
    IdentDistrib (fun ω => (μ ω, D ω)) (fun ω => (μ' ω, D' ω)) P P' := by
  have hd := h.identDistrib_lqgMeasure_with_standardBorel_observable h' hμ hμ' F hF
  have heq : ∀ᵐ ω ∂P, (μ ω, F (fun o => o.1.eval (hC ω) (hcirc ω))) = (μ ω, D ω) :=
    hD.mono fun ω hω => congrArg (Prod.mk (μ ω)) hω
  have heq' : ∀ᵐ ω ∂P', (μ' ω, F (fun o => o.1.eval (hC' ω) (hcirc' ω))) = (μ' ω, D' ω) :=
    hD'.mono fun ω hω => congrArg (Prod.mk (μ' ω)) hω
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq')


end HarmonicBalls

import HarmonicBalls.Proofs.Sec11.LQGJointFieldOpenMassLaw
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Joint law of the LQG measure and field observables -/

namespace HarmonicBalls

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

/-- The LQG measure and any common measurable countable field observable have
one joint law for all realizations of a whole-plane GFF. -/
theorem IsWholePlaneGFF.identDistrib_lqgMeasure_with_observable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (F : (GFFObservable.Admissible → ℝ) → ℕ → ℝ) (hF : Measurable F) :
    IdentDistrib
      (fun ω => (μ ω, F (fun o => o.1.eval (hC ω) (hcirc ω))))
      (fun ω => (μ' ω, F (fun o => o.1.eval (hC' ω) (hcirc' ω)))) P P' := by
  classical
  let _ := h.isProbabilityMeasure
  let _ := h'.isProbabilityMeasure
  let O := {U : Set ℂ // IsOpen U}
  let J := O ⊕ ℕ
  let enc : (Measure ℂ × (ℕ → ℝ)) → J → ℝ≥0∞ := fun p j =>
    match j with
    | .inl U => p.1 U.1
    | .inr n => ENNReal.ofReal (Real.exp (p.2 n))
  have henc : Measurable enc := by
    apply Measurable.of_eval
    intro j
    cases j with
    | inl U => exact (Measure.measurable_coe U.2.measurableSet).comp measurable_fst
    | inr n => exact (((measurable_pi_apply n).comp measurable_snd).exp).ennreal_ofReal
  let X : Ω → Measure ℂ × (ℕ → ℝ) := fun ω =>
    (μ ω, F (fun o => o.1.eval (hC ω) (hcirc ω)))
  let Y : Ω' → Measure ℂ × (ℕ → ℝ) := fun ω =>
    (μ' ω, F (fun o => o.1.eval (hC' ω) (hcirc' ω)))
  have hobs := h.identDistrib_observables_across_spaces h'
  have hXm : AEMeasurable X P := (h.aemeasurable_lqgMeasure hμ).prodMk
    (hF.comp_aemeasurable hobs.aemeasurable_fst)
  have hYm : AEMeasurable Y P' := (h'.aemeasurable_lqgMeasure hμ').prodMk
    (hF.comp_aemeasurable hobs.aemeasurable_snd)
  have hcode : IdentDistrib (enc ∘ X) (enc ∘ Y) P P' := by
    have hx := isProjectiveLimit_map (P := P) (henc.comp_aemeasurable hXm)
    have hy := isProjectiveLimit_map (P := P') (henc.comp_aemeasurable hYm)
    refine ⟨henc.comp_aemeasurable hXm, henc.comp_aemeasurable hYm, ?_⟩
    have heq : (fun I : Finset J => P.map (fun ω (i : I) => enc (X ω) i.1)) =
        (fun I : Finset J => P'.map (fun ω (i : I) => enc (Y ω) i.1)) := by
      funext I
      let U : I → Set ℂ := fun i => match i.1 with | .inl u => u.1 | .inr _ => ∅
      have hU : ∀ i, IsOpen (U i) := by
        intro i
        rcases i with ⟨j, hj⟩
        cases j with
        | inl u => exact u.2
        | inr n => exact isOpen_empty
      let decode : ((I → ℝ≥0∞) × (ℕ → ℝ)) → I → ℝ≥0∞ := fun p i =>
        match i.1 with | .inl _ => p.1 i | .inr n => ENNReal.ofReal (Real.exp (p.2 n))
      have hdecode : Measurable decode := by
        apply Measurable.of_eval
        intro i
        rcases i with ⟨j, hj⟩
        cases j with
        | inl u => exact (measurable_pi_apply (⟨Sum.inl u, hj⟩ : I)).comp measurable_fst
        | inr n => exact (((measurable_pi_apply n).comp measurable_snd).exp).ennreal_ofReal
      have hd := (h.identDistrib_lqg_open_masses_with_observable h' hμ hμ' U hU F hF).comp hdecode
      convert hd.map_eq using 1 <;> congr 1 <;> funext ω i <;>
        cases i with | mk j hj => cases j <;> rfl
    simp only [Finset.restrict_def, Function.comp_def] at hx hy
    rw [heq] at hx
    exact hx.unique hy
  let L := {m : Measure ℂ // IsLocallyFiniteMeasure m} × (ℕ → ℝ)
  let e : L → J → ℝ≥0∞ := fun p => enc (p.1.1, p.2)
  let : MeasurableSpace L := MeasurableSpace.comap e inferInstance
  have hread : Measurable (fun p : L => (p.1.1, p.2)) := by
    apply Measurable.prodMk
    · apply measurable_measure_of_isOpen (fun p : L => p.1.2)
      intro U hU
      exact (measurable_pi_apply (Sum.inl (⟨U, hU⟩ : O))).comp (comap_measurable e)
    · apply Measurable.of_eval
      intro n
      have hv := ((measurable_pi_apply (Sum.inr n : J)).comp (comap_measurable e)).ennreal_toReal
      have hv := hv.log
      simpa [e, enc, ENNReal.toReal_ofReal, (Real.exp_pos _).le] using hv
  refine ⟨hXm, hYm, ?_⟩
  apply Measure.ext
  intro S hS
  obtain ⟨T, hT, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hread hS)
  have hpreX : X ⁻¹' S =ᵐ[P] (enc ∘ X) ⁻¹' T := by
    filter_upwards [hμ] with ω hω
    change (X ω ∈ S) = (enc (X ω) ∈ T)
    have hh := Set.ext_iff.mp heq (⟨⟨μ ω, hω.isLocallyFiniteMeasure⟩, (X ω).2⟩ : L)
    exact propext hh.symm
  have hpreY : Y ⁻¹' S =ᵐ[P'] (enc ∘ Y) ⁻¹' T := by
    filter_upwards [hμ'] with ω hω
    change (Y ω ∈ S) = (enc (Y ω) ∈ T)
    have hh := Set.ext_iff.mp heq (⟨⟨μ' ω, hω.isLocallyFiniteMeasure⟩, (Y ω).2⟩ : L)
    exact propext hh.symm
  rw [Measure.map_apply_of_aemeasurable hXm hS,
    Measure.map_apply_of_aemeasurable hYm hS,
    measure_congr hpreX, measure_congr hpreY,
    ← Measure.map_apply_of_aemeasurable hcode.aemeasurable_fst hT,
    ← Measure.map_apply_of_aemeasurable hcode.aemeasurable_snd hT, hcode.map_eq]


end HarmonicBalls

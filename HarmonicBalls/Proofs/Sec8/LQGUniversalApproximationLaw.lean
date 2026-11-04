import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder

/-! # Universality of circle-average LQG approximations -/

open MeasureTheory Filter ProbabilityTheory

namespace HarmonicBalls

/-- The complete family of admissible observables has the same law for any
 two whole-plane GFFs, even when they are defined on different spaces. -/
theorem IsWholePlaneGFF.identDistrib_observables_across_spaces
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc') :
    IdentDistrib (fun (ω : Ω) (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω))
      (fun (ω : Ω') (o : GFFObservable.Admissible) => o.1.eval (hC' ω) (hcirc' ω)) P P' := by
  let _ := h.isProbabilityMeasure
  let _ := h'.isProbabilityMeasure
  have hm : Measurable (fun (ω : Ω) (o : GFFObservable.Admissible) =>
      o.1.eval (hC ω) (hcirc ω)) := by
    apply Measurable.of_eval
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact h.measurable_pairing φ ho
    | circle r z => exact h.measurable_circle r z ho
  have hm' : Measurable (fun (ω : Ω') (o : GFFObservable.Admissible) =>
      o.1.eval (hC' ω) (hcirc' ω)) := by
    apply Measurable.of_eval
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact h'.measurable_pairing φ ho
    | circle r z => exact h'.measurable_circle r z ho
  refine ⟨hm.aemeasurable, hm'.aemeasurable, ?_⟩
  have hx := isProjectiveLimit_map (P := P) hm.aemeasurable
  have hy := isProjectiveLimit_map (P := P') hm'.aemeasurable
  have heq : (fun I : Finset GFFObservable.Admissible =>
      P.map (fun (ω : Ω) (i : I) => i.1.1.eval (hC ω) (hcirc ω))) =
      (fun I : Finset GFFObservable.Admissible =>
      P'.map (fun (ω : Ω') (i : I) => i.1.1.eval (hC' ω) (hcirc' ω))) := by
    funext I
    exact (h.identDistrib_finite_observables h' Subtype.val).map_eq
  simp only [Finset.restrict_def] at hx hy
  rw [heq] at hx
  exact hx.unique hy

/-- The singular-field circle-average process has a law independent of the
particular realization of the whole-plane GFF. -/
theorem IsWholePlaneGFF.identDistrib_fieldCircleProcess_across_spaces
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc') (α₀ : ℝ) :
    IdentDistrib (fun ω (p : {r : ℝ // 0 < r} × ℂ) =>
      fieldCircleAverage α₀ (hcirc ω) p.1 p.2)
      (fun ω (p : {r : ℝ // 0 < r} × ℂ) =>
        fieldCircleAverage α₀ (hcirc' ω) p.1 p.2) P P' := by
  let v : {r : ℝ // 0 < r} × ℂ → GFFObservable.Admissible :=
    fun p => ⟨.circle p.1 p.2, p.1.2⟩
  let F : (GFFObservable.Admissible → ℝ) → ({r : ℝ // 0 < r} × ℂ → ℝ) :=
    fun f p => f (v p) - α₀ * Real.log (max p.1 ‖p.2‖)
  have hF : Measurable F := Measurable.of_eval fun p =>
    (measurable_pi_apply (v p)).sub measurable_const
  have hd := (h.identDistrib_observables_across_spaces h').comp hF
  convert hd using 1 <;> funext ω p <;>
    exact fieldCircleAverage_eq α₀ _ p.1.property p.2

/-- The full dyadic approximation sequence has the same law for all
realizations of the GFF. -/
theorem IsWholePlaneGFF.identDistrib_lqgApproxSequence_across_spaces
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc') (γ α₀ : ℝ) :
    IdentDistrib
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n))
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀ (hcirc' ω)) (dyadicScale n)) P P' := by
  classical
  choose F hF hFeq using fun n : ℕ => exists_measurable_lqgApprox_decoder γ (dyadicScale n)
  let v : ({r : ℝ // 0 < r} × ℂ → ℝ) → ℕ → Measure ℂ :=
    fun f n => F n (fun z => f (⟨dyadicScale n, dyadicScale_pos n⟩, z))
  have hv : Measurable v := by
    apply Measurable.of_eval
    intro n
    apply (hF n).comp
    apply Measurable.of_eval
    intro z
    exact measurable_pi_apply ((⟨dyadicScale n, dyadicScale_pos n⟩ : {r : ℝ // 0 < r}), z)
  have hd := (h.identDistrib_fieldCircleProcess_across_spaces h' α₀).comp hv
  have hc₁ := ae_all_iff.2 fun n => h.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  have hc₂ := ae_all_iff.2 fun n => h'.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  have heq₁ : (v ∘ fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
      fieldCircleAverage α₀ (hcirc ω) p.1 p.2) =ᵐ[P]
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n)) := by
    filter_upwards [hc₁] with ω hω
    funext n
    exact hFeq n _ (hω n)
  have heq₂ : (v ∘ fun (ω : Ω') (p : {r : ℝ // 0 < r} × ℂ) =>
      fieldCircleAverage α₀ (hcirc' ω) p.1 p.2) =ᵐ[P']
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀ (hcirc' ω)) (dyadicScale n)) := by
    filter_upwards [hc₂] with ω hω
    funext n
    exact hFeq n _ (hω n)
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq₁).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq₂)

end HarmonicBalls

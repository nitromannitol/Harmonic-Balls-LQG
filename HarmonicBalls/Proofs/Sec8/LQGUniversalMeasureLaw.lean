import HarmonicBalls.Proofs.Sec8.LQGUniversalIntegralLaw
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Universality of the LQG measure law -/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- Countable families of open-set masses have a universal joint law. -/
theorem IsWholePlaneGFF.identDistrib_lqg_open_masses_across_spaces
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Countable ι]
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i)) :
    IdentDistrib (fun ω i => μ ω (U i)) (fun ω i => μ' ω (U i)) P P' := by
  classical
  choose f hf hfc hmass using fun i => exists_open_mass_test_functions (hU i)
  let F : (ι × ℕ → ℝ) → ι → ℝ≥0∞ := fun x i => ⨆ n, ENNReal.ofReal (x (i, n))
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro i
    exact Measurable.iSup fun n => (measurable_pi_apply (i, n)).ennreal_ofReal
  have hd := (h.identDistrib_lqg_integrals_across_spaces h' hμ hμ'
    (f := fun p : ι × ℕ => f p.1 p.2) (fun p => hf p.1 p.2)
    (fun p => hfc p.1 p.2)).comp hF
  have heq₁ : (F ∘ fun ω p => ∫ z, f p.1 p.2 z ∂(μ ω)) =ᵐ[P]
      (fun ω i => μ ω (U i)) := by
    filter_upwards [hμ] with ω hω
    funext i
    exact (hmass i (μ ω) hω.isLocallyFiniteMeasure).symm
  have heq₂ : (F ∘ fun ω p => ∫ z, f p.1 p.2 z ∂(μ' ω)) =ᵐ[P']
      (fun ω i => μ' ω (U i)) := by
    filter_upwards [hμ'] with ω hω
    funext i
    exact (hmass i (μ' ω) hω.isLocallyFiniteMeasure).symm
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq₁).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq₂)

/-- The limiting LQG measures have the same law on different probability
spaces whenever the field parameters agree. -/
theorem IsWholePlaneGFF.identDistrib_lqgMeasure_across_spaces
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ') :
    IdentDistrib μ μ' P P' := by
  classical
  let O := {U : Set ℂ // IsOpen U}
  let F : Measure ℂ → O → ℝ≥0∞ := fun m U => m U.1
  have hF : Measurable F := Measurable.of_eval fun U => Measure.measurable_coe U.2.measurableSet
  have hd : IdentDistrib (F ∘ μ) (F ∘ μ') P P' := by
    let _ := h.isProbabilityMeasure
    let _ := h'.isProbabilityMeasure
    have hx := isProjectiveLimit_map (P := P) (hF.comp_aemeasurable (h.aemeasurable_lqgMeasure hμ))
    have hy := isProjectiveLimit_map (P := P') (hF.comp_aemeasurable (h'.aemeasurable_lqgMeasure hμ'))
    refine ⟨hF.comp_aemeasurable (h.aemeasurable_lqgMeasure hμ),
      hF.comp_aemeasurable (h'.aemeasurable_lqgMeasure hμ'), ?_⟩
    have heq : (fun I : Finset O => P.map (fun ω (i : I) => μ ω i.1.1)) =
        (fun I : Finset O => P'.map (fun ω (i : I) => μ' ω i.1.1)) := by
      funext I
      exact (h.identDistrib_lqg_open_masses_across_spaces h' hμ hμ'
        (fun i : I => i.1.1) (fun i => i.1.2)).map_eq
    simp only [Finset.restrict_def, Function.comp_def, F] at hx hy
    rw [heq] at hx
    exact hx.unique hy
  let L := {m : Measure ℂ // IsLocallyFiniteMeasure m}
  let e : L → O → ℝ≥0∞ := fun m => F m.1
  let : MeasurableSpace L := MeasurableSpace.comap e inferInstance
  have hcoe : Measurable (Subtype.val : L → Measure ℂ) := by
    apply measurable_measure_of_isOpen (fun m => m.2)
    intro U hU
    exact (measurable_pi_apply (⟨U, hU⟩ : O)).comp (comap_measurable e)
  refine ⟨h.aemeasurable_lqgMeasure hμ, h'.aemeasurable_lqgMeasure hμ', ?_⟩
  apply Measure.ext
  intro S hS
  obtain ⟨T, hT, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hcoe hS)
  have hpreX : μ ⁻¹' S =ᵐ[P] (F ∘ μ) ⁻¹' T := by
    filter_upwards [hμ] with ω hω
    change (μ ω ∈ S) = (F (μ ω) ∈ T)
    have hx := Set.ext_iff.mp heq (⟨μ ω, hω.isLocallyFiniteMeasure⟩ : L)
    exact propext hx.symm
  have hpreY : μ' ⁻¹' S =ᵐ[P'] (F ∘ μ') ⁻¹' T := by
    filter_upwards [hμ'] with ω hω
    change (μ' ω ∈ S) = (F (μ' ω) ∈ T)
    have hy := Set.ext_iff.mp heq (⟨μ' ω, hω.isLocallyFiniteMeasure⟩ : L)
    exact propext hy.symm
  rw [Measure.map_apply_of_aemeasurable (h.aemeasurable_lqgMeasure hμ) hS,
    Measure.map_apply_of_aemeasurable (h'.aemeasurable_lqgMeasure hμ') hS,
    measure_congr hpreX, measure_congr hpreY,
    ← Measure.map_apply_of_aemeasurable hd.aemeasurable_fst hT,
    ← Measure.map_apply_of_aemeasurable hd.aemeasurable_snd hT, hd.map_eq]

end HarmonicBalls

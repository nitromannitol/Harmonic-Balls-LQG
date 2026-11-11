import HarmonicBalls.Proofs.Sec11.LQGJointStandardBorelLaw
import HarmonicBalls.Steps.Sec11.LocalPairingLaw
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # The base LQG metric as a field observable -/

namespace HarmonicBalls

open Set MeasureTheory ProbabilityTheory

/-- Every standard Borel observable measurable in the distribution sigma algebra
has a common measurable representation in the full GFF observable process.
The representation is independent of the circle-average coordinates. -/
theorem exists_common_observable_of_distribution_measurable
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (f : ((ℂ → ℝ) → ℝ) → E)
    (hf : Measurable[distributionMeasurableSpace] f) :
    ∃ F : (GFFObservable.Admissible → ℝ) → E, Measurable F ∧
      ∀ T c, F (fun o => o.1.eval T c) = f T := by
  let p : ((ℂ → ℝ) → ℝ) → LocalFieldTest univ → ℝ :=
    localFieldPairings 0 id univ
  have hσ : distributionMeasurableSpace = MeasurableSpace.comap p inferInstance := by
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    simp [distributionMeasurableSpace, fieldSigmaAlgebra, fieldPairing]
  rw [hσ] at hf
  obtain ⟨g, hg, heq⟩ := hf.exists_eq_measurable_comp
  let r : (GFFObservable.Admissible → ℝ) → LocalFieldTest univ → ℝ :=
    fun v φ => v ⟨.pairing φ.1, φ.2⟩
  have hr : Measurable r := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨.pairing φ.1, φ.2⟩ : GFFObservable.Admissible)
  refine ⟨g ∘ r, hg.comp hr, ?_⟩
  intro T c
  have hpr : r (fun o => o.1.eval T c) = p T := by
    funext φ
    simp [r, p, localFieldPairings, fieldPairing, GFFObservable.eval]
  rw [Function.comp_apply, hpr, heq]
  rfl

/-- The base metric has a common measurable continuous-distance decoder on
all fields for which its distance function is continuous.  On other fields the
decoder is an arbitrary measurable extension. -/
theorem IsLQGMetric.exists_common_continuous_observable
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ F : (GFFObservable.Admissible → ℝ) → C(ℂ × ℂ, ℝ), Measurable F ∧
      ∀ T c (hcont : Continuous (fun p : ℂ × ℂ => 𝔇 T p.1 p.2)),
        F (fun o => o.1.eval T c) = ⟨fun p => 𝔇 T p.1 p.2, hcont⟩ := by
  let d : ℕ → ℂ × ℂ := TopologicalSpace.denseSeq (ℂ × ℂ)
  let e : C(ℂ × ℂ, ℝ) → ℕ → ℝ := fun D n => D (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n =>
    (continuous_eval_const (d n)).measurable
  have hinj : Function.Injective e := by
    intro D D' h
    apply ContinuousMap.ext
    have hd := (TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)).equalizer
      D.continuous D'.continuous
    apply congrFun (hd ?_)
    funext n
    exact congrFun h n
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hinj
  obtain ⟨decode, hdecode, hdecode_eq⟩ :=
    hemb.exists_measurable_extend (g := id) measurable_id (fun _ => inferInstance)
  let f : ((ℂ → ℝ) → ℝ) → ℕ → ℝ := fun T n => 𝔇 T (d n).1 (d n).2
  have hf : Measurable[distributionMeasurableSpace] f := by
    let : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
    exact measurable_pi_iff.mpr fun n => h𝔇.measurable_apply (d n).1 (d n).2
  obtain ⟨G, hG, hG_eq⟩ := exists_common_observable_of_distribution_measurable f hf
  refine ⟨decode ∘ G, hdecode.comp hG, ?_⟩
  intro T c hcont
  rw [Function.comp_apply, hG_eq]
  have heq : f T = e ⟨fun p => 𝔇 T p.1 p.2, hcont⟩ := rfl
  rw [heq]
  exact congrFun hdecode_eq _

/-- The LQG measure and any countable collection of distances of the same
base metric functional have a realization-independent joint law. -/
theorem IsWholePlaneGFF.identDistrib_lqgMeasure_baseMetric_values
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (z w : ℕ → ℂ) :
    IdentDistrib (fun ω => (μ ω, fun n => 𝔇 (hC ω) (z n) (w n)))
      (fun ω => (μ' ω, fun n => 𝔇 (hC' ω) (z n) (w n))) P P' := by
  let f : ((ℂ → ℝ) → ℝ) → ℕ → ℝ := fun T n => 𝔇 T (z n) (w n)
  have hf : Measurable[distributionMeasurableSpace] f := by
    let : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
    exact measurable_pi_iff.mpr fun n => h𝔇.measurable_apply (z n) (w n)
  obtain ⟨F, hF, hF_eq⟩ := exists_common_observable_of_distribution_measurable f hf
  have hd := h.identDistrib_lqgMeasure_with_standardBorel_observable h' hμ hμ' F hF
  simpa only [hF_eq] using hd

/-- Continuous versions of one base metric functional and their LQG measures
have the same joint law in any two whole-plane GFF realizations. -/
theorem IsWholePlaneGFF.identDistrib_lqgMeasure_baseMetric
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ α₀ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    {D : Ω → C(ℂ × ℂ, ℝ)} {D' : Ω' → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ p, D ω p = 𝔇 (hC ω) p.1 p.2)
    (hD' : ∀ᵐ ω ∂P', ∀ p, D' ω p = 𝔇 (hC' ω) p.1 p.2) :
    IdentDistrib (fun ω => (μ ω, D ω)) (fun ω => (μ' ω, D' ω)) P P' := by
  obtain ⟨F, hF, hF_eq⟩ := h𝔇.exists_common_continuous_observable
  apply h.identDistrib_lqgMeasure_metric_of_common_observable h' hμ hμ' F hF
  · filter_upwards [hD] with ω hω
    have heq : (fun p : ℂ × ℂ => 𝔇 (hC ω) p.1 p.2) = D ω := funext fun p => (hω p).symm
    have hc : Continuous (fun p : ℂ × ℂ => 𝔇 (hC ω) p.1 p.2) := heq ▸ (D ω).continuous
    rw [hF_eq _ _ hc]
    exact ContinuousMap.ext (fun p => (hω p).symm)
  · filter_upwards [hD'] with ω hω
    have heq : (fun p : ℂ × ℂ => 𝔇 (hC' ω) p.1 p.2) = D' ω := funext fun p => (hω p).symm
    have hc : Continuous (fun p : ℂ × ℂ => 𝔇 (hC' ω) p.1 p.2) := heq ▸ (D' ω).continuous
    rw [hF_eq _ _ hc]
    exact ContinuousMap.ext (fun p => (hω p).symm)


end HarmonicBalls

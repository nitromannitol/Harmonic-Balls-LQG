import HarmonicBalls.Proofs.GFF.UnrepresentableGFF

/-!
# Unconditional GFF version counterexamples

Leonardo Bonanno's normalized whole-plane GFF construction supplies the starting
probability space. A product modification preserves each fixed-test pairing
almost surely, while simultaneous distribution representation fails almost surely.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

/-- A canonical-existence witness together with its fixed-test-equivalent product version. -/
theorem exists_projectWholePlaneGFF_unrepresentable_modification :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
      (_ : IsProbabilityMeasure P) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ)
      (hC' : Ω × ℝ → (ℂ → ℝ) → ℝ),
      IsWholePlaneGFF P hC hcirc ∧
      IsWholePlaneGFF (P.prod (gaussianReal 0 1)) hC' (fun p => hcirc p.1) ∧
      (∀ φ, (fun p : Ω × ℝ => hC p.1 φ) =ᵐ[P.prod (gaussianReal 0 1)]
        (fun p => hC' p φ)) ∧
      ∀ᵐ p ∂P.prod (gaussianReal 0 1), ¬ ∃ distribution : PlaneDistribution,
        RepresentsPlaneDistribution (hC' p) distribution := by
  obtain ⟨Ω, m, P, hP, hC, hcirc, hh⟩ := exists_projectWholePlaneGFF
  let : MeasurableSpace Ω := m
  let : IsProbabilityMeasure P := hP
  obtain ⟨hC', hg, he, hn⟩ := hh.product_has_ae_unrepresentable_modification
  exact ⟨Ω, m, P, hP, hC, hcirc, hC', hh, hg, he, hn⟩

/-- There is a probability space carrying a project GFF with no samplewise
simultaneous distribution representative on a full-measure event. -/
theorem exists_projectWholePlaneGFF_ae_unrepresentable :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
      (_ : IsProbabilityMeasure P) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc ∧
      ∀ᵐ ω ∂P, ¬ ∃ distribution : PlaneDistribution,
        RepresentsPlaneDistribution (hC ω) distribution := by
  obtain ⟨Ω, m, P, hP, hC, hcirc, hC', _, hg, _, hn⟩ :=
    exists_projectWholePlaneGFF_unrepresentable_modification
  let : MeasurableSpace Ω := m
  let : IsProbabilityMeasure P := hP
  exact ⟨Ω × ℝ, inferInstance, P.prod (gaussianReal 0 1), inferInstance,
    hC', (fun p => hcirc p.1), hg, hn⟩

/-- Leonardo Bonanno's existence theorem also yields a GFF version for which
all current metric extensions are simultaneously Euclidean almost surely. -/
theorem exists_projectWholePlaneGFF_ae_euclidean_metric_extension :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
      (_ : IsProbabilityMeasure P) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc ∧
      ∀ᵐ ω ∂P, ∀ (metric : PlaneDistribution → ContinuousPlaneMetric) z w,
        extendPlaneMetricMap metric (hC ω) z w = dist z w := by
  obtain ⟨Ω, m, P, hP, hC, hcirc, hh⟩ := exists_projectWholePlaneGFF
  let : MeasurableSpace Ω := m
  let : IsProbabilityMeasure P := hP
  obtain ⟨hC', hg, _, he⟩ := hh.product_has_ae_euclidean_metric_extension
  exact ⟨Ω × ℝ, inferInstance, P.prod (gaussianReal 0 1), inferInstance,
    hC', (fun p => hcirc p.1), hg, he⟩

/-- Almost-sure unrepresentability excludes even an arbitrary simultaneous
representative, and hence excludes a measurable one. -/
theorem not_exists_ae_simultaneous_representation
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ}
    (h : ∀ᵐ ω ∂P, ¬ ∃ distribution : PlaneDistribution,
      RepresentsPlaneDistribution (hC ω) distribution) :
    ¬ ∃ field : Ω → PlaneDistribution,
      ∀ᵐ ω ∂P, RepresentsPlaneDistribution (hC ω) (field ω) := by
  rintro ⟨field, hf⟩
  have hfalse : ∀ᵐ ω ∂P, False := by
    filter_upwards [h, hf] with ω hn hr
    exact hn ⟨field ω, hr⟩
  obtain ⟨_, contradiction⟩ := hfalse.exists
  exact contradiction


end HarmonicBalls

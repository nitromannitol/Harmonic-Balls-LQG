import HarmonicBalls.Proofs.GFF.PfefferAroundRepresentation

/-! # Almost everywhere measurable around distances

Pointwise almost everywhere measurable distances admit a common measurable
continuous metric representative, yielding measurability of around distances.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A random Euclidean length metric with almost everywhere measurable point
values has one measurable continuous representative agreeing at all pairs
on a common full-measure event. -/
theorem exists_measurable_continuousMap_of_ae_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hpoint : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ F : Ω → C(ℂ × ℂ, ℝ), Measurable F ∧
      (∀ ω, IsEuclideanLengthMetric fun x y => F ω (x, y)) ∧
      ∀ᵐ ω ∂P, ∀ x y, F ω (x, y) = D ω x y := by
  classical
  let E : Ω → ℂ → ℂ → ℝ := fun ω =>
    if IsEuclideanLengthMetric (D ω) then D ω else dist
  have hE : ∀ ω, IsEuclideanLengthMetric (E ω) := by
    intro ω
    by_cases h : IsEuclideanLengthMetric (D ω)
    · simp [E, h]
    · simpa [E, h] using isEuclideanLengthMetric_dist
  let K : Ω → C(ℂ × ℂ, ℝ) := fun ω =>
    ⟨fun p => E ω p.1 p.2, (hE ω).continuous_pair⟩
  have hK : AEMeasurable K P := by
    have hn : NullMeasurable K P := by
      change @Measurable (NullMeasurableSpace Ω P) _ _ _ K
      apply ContinuousMap.measurable_iff_eval.mpr
      intro p
      have hp : AEMeasurable (fun ω => K ω p) P := by
        apply (hpoint p.1 p.2).congr
        filter_upwards [hmetric] with ω hω
        simp [K, E, hω]
      exact hp.nullMeasurable.measurable'
    exact hn.aemeasurable
  let M := hK.mk K
  have hM : Measurable M := hK.measurable_mk
  have hMeq : ∀ᵐ ω ∂P, M ω = K ω := hK.ae_eq_mk.symm
  let H : Set Ω := {ω | IsEuclideanLengthMetric fun x y => M ω (x, y)}
  have hHae : ∀ᵐ ω ∂P, ω ∈ H := by
    filter_upwards [hMeq] with ω hω
    simpa [H, hω, K] using hE ω
  have hH : NullMeasurableSet H P := by
    apply (nullMeasurableSet_univ (μ := P)).congr
    filter_upwards [hHae] with ω hω
    simp [hω]
  obtain ⟨G, hsub, hG, hGae⟩ := hH.exists_measurable_subset_ae_eq
  have hGfull : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hGae, hHae] with ω heq hω
    exact Eq.mpr heq hω
  let F : Ω → C(ℂ × ℂ, ℝ) := fun ω =>
    if ω ∈ G then M ω else ⟨fun p => dist p.1 p.2, continuous_dist⟩
  refine ⟨F, Measurable.ite hG hM measurable_const, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ G
    · simpa [F, hω, H] using hsub hω
    · simpa [F, hω] using isEuclideanLengthMetric_dist
  · filter_upwards [hGfull, hMeq, hmetric] with ω hω heq hm x y
    simp [F, hω, heq, K, E, hm]

/-- The unrestricted around distance at fixed center and radii is almost
everywhere measurable under almost everywhere measurable point distances. -/
theorem aemeasurable_pfefferAround_of_ae_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {D : Ω → ℂ → ℂ → ℝ} (center : ℂ) (a b : ℝ)
    (hpoint : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    AEMeasurable (fun ω => pfefferAround (D ω) center a b) P := by
  obtain ⟨F, hF, hFm, hFeq⟩ :=
    exists_measurable_continuousMap_of_ae_pointwise hpoint hmetric
  have hm := aemeasurable_pfefferAround_of_ae_euclideanLengthMetric center a b
    (P := P) (D := fun ω x y => F ω (x, y))
    (fun x y => (ContinuousMap.measurable_eval (x, y)).comp hF)
    (Filter.Eventually.of_forall hFm)
  apply hm.congr
  filter_upwards [hFeq] with ω hω
  have heq : (fun x y => F ω (x, y)) = D ω := by
    funext x y
    exact hω x y
  rw [heq]

end HarmonicBalls

import HarmonicBalls.Proofs.Sec11.Closure.MetricBridgeZero

/-!
# Measurable version of the zero-charge metric bridge (Section 11)

For `Ω : Type`, a whole-plane GFF `hC` has pairings `ω ↦ hC ω φ` measurable for every test function `φ`
(`IsWholePlaneGFF.measurable_pairing`). Hence `hC` is measurable for `distributionMeasurableSpace`, the
σ-algebra of pairing functionals (`Defs/LQGMetric.lean`), and the canonical metric `ω ↦ 𝔇 (hC ω) z w` of an
`IsLQGMetric` is measurable (`IsLQGMetric.measurable_apply`). Combined with the almost-sure bridge of
`Closure/MetricBridgeZero.lean`, an arbitrary metric map `D` with `IsLQGMetricOfField P γ ξ 0 hC D` agrees almost
surely with a field `D'` whose entries are measurable and which is a Euclidean length metric almost surely. This
is the form in which the conditional chain of Lemma 11.12 consumes the metric.
-/

namespace HarmonicBalls

open MeasureTheory

/-- A map into the space of pairing functionals is measurable for `distributionMeasurableSpace` when all its
pairings are measurable (the σ-algebra is the supremum of the pairing σ-algebras). -/
lemma measurable_distribution_of_pairings {Ω : Type} [MeasurableSpace Ω]
    {hC : Ω → (ℂ → ℝ) → ℝ}
    (hpair : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ) :
    @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun φ hφ => ?_
  exact (hpair φ hφ).comap_le

/-- The canonical metric of a whole-plane GFF is measurable in the field: `ω ↦ 𝔇 (hC ω) z w` is measurable. -/
lemma measurable_canonical_metric {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (z w : ℂ) :
    Measurable fun ω => 𝔇 (hC ω) z w :=
  (h𝔇.measurable_apply z w).comp (measurable_distribution_of_pairings h.measurable_pairing)

/-- Measurable version of the zero-charge metric bridge: an arbitrary metric map `D` with
`IsLQGMetricOfField P γ ξ 0 hC D` agrees almost surely with a field `D'` whose entries are measurable, and
`D' ω` is a Euclidean length metric almost surely. -/
theorem exists_measurable_metric_ae_eq_of_isLQGMetricOfField_zero {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ 0 hC D) :
    ∃ D' : Ω → ℂ → ℂ → ℝ, (∀ x y, Measurable fun ω => D' ω x y) ∧
      (∀ᵐ ω ∂P, D ω = D' ω) ∧ (∀ᵐ ω ∂P, IsEuclideanLengthMetric (D' ω)) := by
  obtain ⟨𝔇, h𝔇, hbridge⟩ := ae_metric_eq_canonical_of_isLQGMetricOfField_zero h hD
  refine ⟨fun ω => 𝔇 (hC ω), fun x y => measurable_canonical_metric h 𝔇 h𝔇 x y, ?_, ?_⟩
  · filter_upwards [hbridge] with ω hω
    show D ω = 𝔇 (hC ω)
    exact hω
  · filter_upwards [ae_isEuclideanLengthMetric_of_isLQGMetricOfField_zero h hD, hbridge] with ω h1 h2
    show IsEuclideanLengthMetric (𝔇 (hC ω))
    rw [← h2]
    exact h1


end HarmonicBalls

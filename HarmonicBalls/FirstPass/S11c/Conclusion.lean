import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Proposition 11.10: the measurable event of the conclusion from the Cameron-Martin transfer

The conclusion of Proposition 11.10 asks for a measurable event `A` of positive probability
on which `sup_{u,v ∈ S₂} D(u,v; S₂) ≤ c` and `C ≤ μ(S₁)`. The frozen Cameron-Martin event transfer
`CameronMartinEventTransferFrozen` gives positive probability of the unshifted event, which is null-measurable under the
measurability hypotheses; this file passes from a null-measurable event of positive probability to a measurable subset of
the same measure, and writes the supremum in the form of the Draft statement.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- A null-measurable set of positive measure contains a measurable set of the same measure. -/
lemma exists_measurable_subset_of_nullMeasurableSet_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {s : Set Ω} (hs : NullMeasurableSet s P) (hpos : 0 < P s) :
    ∃ A ⊆ s, MeasurableSet A ∧ 0 < P A := by
  obtain ⟨t, htm, hst⟩ := hs
  have hbad : P {ω | ¬ (ω ∈ s ↔ ω ∈ t)} = 0 := ae_iff.1 (Filter.eventuallyEqSet_iff.1 hst)
  have hsub : t \ s ⊆ {ω | ¬ (ω ∈ s ↔ ω ∈ t)} := fun ω hω h => hω.2 (h.2 hω.1)
  have hdiff : P (t \ s) = 0 := measure_mono_null hsub hbad
  obtain ⟨N, hsubN, hNm, hN0⟩ := exists_measurable_superset_of_null hdiff
  refine ⟨t \ N, fun ω hω => ?_, htm.diff hNm, ?_⟩
  · by_contra hns
    exact hω.2 (hsubN ⟨hω.1, hns⟩)
  · rw [measure_sdiff_null hN0, ← measure_congr hst]
    exact hpos

/-- The supremum of the internal metric over `S × S` is at most `c` exactly when every pair of points of `S` is. -/
lemma iSup₂_internalMetric_le_iff {X : Type*} {S : Set X} {F : X → X → ℝ≥0∞} {c : ℝ≥0∞} :
    (⨆ u ∈ S, ⨆ v ∈ S, F u v) ≤ c ↔ ∀ u ∈ S, ∀ v ∈ S, F u v ≤ c := by
  simp only [iSup₂_le_iff]

/-- Proposition 11.10 (conclusion), from the frozen Cameron-Martin event transfer: if the shifted event
`{sup_{S₂} shifted metric ≤ c, C ≤ shifted mass of S₁}` is null-measurable and has positive probability, then the unshifted
event `{∀ u v ∈ S₂, D(u,v; S₂) ≤ c, C ≤ μ(S₁)}` contains a measurable event of positive probability. -/
theorem exists_measurable_of_cameronMartin_transfer (hCM : CameronMartinEventTransferFrozen.{u})
    {γ α₀ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (f : ℂ → ℝ)
    (hf1 : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : HasCompactSupport f) (hf3 : ∀ z : ℂ, ‖z‖ = 1 → f z = 0)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) {S₁ S₂ : Set ℂ} (c C : ℝ≥0∞)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) (hS₁ : IsClosedDyadicSquare S₁) (hS₂ : IsClosedDyadicSquare S₂)
    (hsup : AEMeasurable (fun ω => ⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (D ω) S₂ u v) P)
    (hmass : AEMeasurable (fun ω => μ ω S₁) P)
    (hshiftNM : NullMeasurableSet {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂,
      internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ c ∧
      C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} P)
    (hshiftpos : 0 < P {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂,
      internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ c ∧
      C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁}) :
    ∃ A ⊆ {ω | (∀ u ∈ S₂, ∀ v ∈ S₂, internalMetric (D ω) S₂ u v ≤ c) ∧ C ≤ μ ω S₁},
      MeasurableSet A ∧ 0 < P A := by
  have hpos := hCM γ α₀ ξ f hγ hγ2 hα hf1 hf2 hf3 Ω P hC hcirc μ D S₁ S₂ c C hGFF hμ hD hS₁ hS₂
    hsup hmass hshiftNM hshiftpos
  have hNM : NullMeasurableSet {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (D ω) S₂ u v) ≤ c ∧
      C ≤ μ ω S₁} P :=
    (nullMeasurableSet_le hsup aemeasurable_const).inter (nullMeasurableSet_le aemeasurable_const hmass)
  obtain ⟨A, hAsub, hAm, hApos⟩ := exists_measurable_subset_of_nullMeasurableSet_pos P hNM hpos
  refine ⟨A, fun ω hω => ?_, hAm, hApos⟩
  obtain ⟨h1, h2⟩ := hAsub hω
  exact ⟨iSup₂_internalMetric_le_iff.1 h1, h2⟩

end HarmonicBalls

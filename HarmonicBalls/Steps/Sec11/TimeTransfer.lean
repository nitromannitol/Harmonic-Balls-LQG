import Mathlib

/-! # Transferring almost-everywhere statements through first-entry times -/

namespace HarmonicBalls

open MeasureTheory Set Filter

/-- A measurable map sends a full-measure set to a full-measure image when
its image is measurable. The target predicate need not be measurable. -/
theorem ae_map_of_ae_mem_image {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (s : Set X) (P : Y → Prop)
    (hf : AEMeasurable f μ) (hsimage : MeasurableSet (f '' s))
    (hsfull : ∀ᵐ x ∂μ, x ∈ s) (hP : ∀ x ∈ s, P (f x)) :
    ∀ᵐ y ∂(μ.map f), P y := by
  have himage : ∀ᵐ y ∂(μ.map f), y ∈ f '' s :=
    (ae_map_iff hf hsimage).2 (hsfull.mono fun x hx => ⟨x, hx, rfl⟩)
  filter_upwards [himage] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hP x hx

/-- A full-measure σ-compact set on which the map is continuous suffices to
transfer an arbitrary pointwise property to almost every image point. This is
a measure-theoretic endpoint for Section 11; existence of such a set for the
entry-time map is a separate step. -/
theorem ae_map_of_sigmaCompact_full_set
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (s : Set X) (P : ℝ → Prop)
    (hf : AEMeasurable f μ) (hs : IsSigmaCompact s) (hcont : ContinuousOn f s)
    (hsfull : ∀ᵐ x ∂μ, x ∈ s) (hP : ∀ x ∈ s, P (f x)) :
    ∀ᵐ y ∂(μ.map f), P y := by
  have himage : MeasurableSet (f '' s) := by
    obtain ⟨K, hK, hcover⟩ := hs.image_of_continuousOn hcont
    rw [← hcover]
    exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet
  exact ae_map_of_ae_mem_image μ f s P hf himage hsfull hP

/-- A countable compact cover of full measure on which the map is continuous
piecewise also transfers an arbitrary property. The map need not be continuous
on the union of the compact sets. -/
theorem ae_map_of_countable_compact_full_cover
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (K : ℕ → Set X) (P : ℝ → Prop)
    (hf : AEMeasurable f μ) (hK : ∀ n, IsCompact (K n))
    (hcont : ∀ n, ContinuousOn f (K n))
    (hfull : ∀ᵐ x ∂μ, x ∈ ⋃ n, K n)
    (hP : ∀ n x, x ∈ K n → P (f x)) : ∀ᵐ y ∂(μ.map f), P y := by
  have himage : MeasurableSet (f '' (⋃ n, K n)) := by
    rw [image_iUnion]
    exact MeasurableSet.iUnion fun n => ((hK n).image_of_continuousOn (hcont n)).isClosed.measurableSet
  apply ae_map_of_ae_mem_image μ f (⋃ n, K n) P hf himage hfull
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  exact hP n x hn

end HarmonicBalls

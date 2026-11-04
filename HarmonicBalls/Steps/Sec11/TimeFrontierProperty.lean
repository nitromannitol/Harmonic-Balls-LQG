import HarmonicBalls.Steps.Sec11.TimeFamily
import HarmonicBalls.Steps.Sec11.TimeTransferAE

/-! # Transfer of boundary-point properties to almost every time -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- Any pointwise property at positive-time frontiers transfers to almost every
positive time for an almost-everywhere exhausting harmonic-ball family. No
measurability assumption on the property is needed. -/
theorem ae_time_property_of_ae_frontier_of_ae_cover
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (Λ : ℝ → Set ℂ) (z₀ : ℂ)
    (hfamily : SatisfiesHarmonicBallConditions μ Λ z₀)
    (hcover : ∀ᵐ z ∂μ, ∃ t, 0 < t ∧ z ∈ Λ t)
    (P : ℝ → Prop)
    (hpoint : ∀ᵐ z ∂μ, ∀ t : ℝ, 0 < t → z ∈ frontier (Λ t) → P t) :
    ∀ᵐ t ∂volume, 0 < t → P t := by
  let τ : ℂ → ℝ := fun z => sInf {t : ℝ | 0 < t ∧ z ∈ Λ t}
  have hopen : ∀ t, 0 < t → IsOpen (Λ t) := fun t ht => (hfamily.isRegularOpen t ht).isOpen
  have hτ : AEMeasurable τ μ := (measurable_positive_entry_time_without_cover Λ hopen).aemeasurable
  have ⟨hmap, hfrontier⟩ := hfamily.entry_time_law_and_frontier hcover
  have hcont : ∀ᵐ z ∂μ, ContinuousAt τ z := hfrontier.mono fun _ h => h.1
  have hprop : ∀ᵐ z ∂μ, 0 < τ z → P (τ z) := by
    filter_upwards [hfrontier, hpoint] with z hz hp
    exact fun ht => hp (τ z) ht (hz.2 ht)
  have hp : ∀ᵐ t ∂(μ.map τ), 0 < t → P t :=
    ae_map_of_ae_continuousAt μ τ _ hτ hcont hprop
  rw [hmap] at hp
  have hvol := (ae_restrict_iff' measurableSet_Ioi).1 hp
  filter_upwards [hvol] with t ht hpos
  exact ht hpos hpos

/-- The boundary-to-time transfer holds without an exhaustion assumption by
restricting the measure to the union of the positive-time balls. -/
theorem ae_time_property_of_ae_frontier
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (Λ : ℝ → Set ℂ) (z₀ : ℂ)
    (hfamily : SatisfiesHarmonicBallConditions μ Λ z₀)
    (P : ℝ → Prop)
    (hpoint : ∀ᵐ z ∂μ, ∀ t : ℝ, 0 < t → z ∈ frontier (Λ t) → P t) :
    ∀ᵐ t ∂volume, 0 < t → P t := by
  let U : Set ℂ := ⋃ t ∈ Ioi (0 : ℝ), Λ t
  have hopen : ∀ t, 0 < t → IsOpen (Λ t) := fun t ht => (hfamily.isRegularOpen t ht).isOpen
  have hU : IsOpen U := isOpen_iUnion fun t => isOpen_iUnion fun ht => hopen t ht
  have hsubset : ∀ t, 0 < t → Λ t ⊆ U := by
    intro t ht x hx
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hx⟩⟩
  have hfamily' : SatisfiesHarmonicBallConditions (μ.restrict U) Λ z₀ :=
    { hfamily with
      measure_eq := by
        intro t ht
        rw [Measure.restrict_apply (hopen t ht).measurableSet, inter_eq_left.mpr (hsubset t ht)]
        exact hfamily.measure_eq t ht
      measure_frontier := by
        intro t ht
        apply le_antisymm _ bot_le
        calc
          (μ.restrict U) (frontier (Λ t)) ≤ μ (frontier (Λ t)) := Measure.restrict_apply_le U _
          _ = 0 := hfamily.measure_frontier t ht }
  have hcover : ∀ᵐ z ∂(μ.restrict U), ∃ t, 0 < t ∧ z ∈ Λ t := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    simp only [U, mem_iUnion, mem_Ioi] at hz
    obtain ⟨t, ht, hzt⟩ := hz
    exact ⟨t, ht, hzt⟩
  exact ae_time_property_of_ae_frontier_of_ae_cover (μ.restrict U) Λ z₀ hfamily' hcover P
    (ae_restrict_of_ae hpoint)

end HarmonicBalls

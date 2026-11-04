import Mathlib

/-! # Compact covers of almost-everywhere properties -/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- A conull property for a σ-finite compact-inner-regular measure holds on a
countable union of compact sets of full measure. -/
theorem exists_compact_full_cover_of_ae
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] [Measure.InnerRegularCompactLTTop μ]
    (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧
      (∀ n x, x ∈ K n → P x) ∧ (∀ᵐ x ∂μ, x ∈ ⋃ n, K n) := by
  classical
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  let S : ℕ → Set X := fun n => Nᶜ ∩ spanningSets μ n
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => hNmeas.compl.inter (measurableSet_spanningSets μ n)
  have hSfinite : ∀ n, μ (S n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne (measure_mono inter_subset_right)
  have hex : ∀ n k : ℕ, ∃ K : Set X, K ⊆ S n ∧ IsCompact K ∧
      μ (S n \ K) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro n k
    apply (hSmeas n).exists_isCompact_sdiff_lt (hSfinite n)
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  choose L hLsub hLcompact hLsmall using hex
  let V : Set X := ⋃ n, ⋃ k, L n k
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdiff : ∀ n, μ (S n \ V) = 0 := by
    intro n
    apply le_antisymm _ bot_le
    apply ge_of_tendsto' hlim
    intro k
    apply le_of_lt
    calc
      μ (S n \ V) ≤ μ (S n \ L n k) := by
        apply measure_mono
        intro x hx
        exact ⟨hx.1, fun h => hx.2 (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨k, h⟩⟩)⟩
      _ < _ := hLsmall n k
  have hfull : μ Vᶜ = 0 := by
    have hsub : Vᶜ ⊆ N ∪ ⋃ n, (S n \ V) := by
      intro x hx
      by_cases hn : x ∈ N
      · exact Or.inl hn
      · right
        have hxspan : x ∈ ⋃ n, spanningSets μ n := by rw [iUnion_spanningSets]; trivial
        obtain ⟨n, hxn⟩ := mem_iUnion.mp hxspan
        exact mem_iUnion.mpr ⟨n, ⟨⟨hn, hxn⟩, hx⟩⟩
    apply measure_mono_null hsub
    exact measure_union_null hNzero (measure_iUnion_null hdiff)
  let K : ℕ → Set X := fun j => L (Nat.unpair j).1 (Nat.unpair j).2
  refine ⟨K, ?_, ?_, ?_⟩
  · intro j
    exact hLcompact _ _
  · intro j x hx
    have hxN : x ∉ N := (hLsub _ _ hx).1
    by_contra hn
    exact hxN (hNsub hn)
  · have hz : μ (⋃ n, K n)ᶜ = 0 := by
      apply measure_mono_null _ hfull
      intro x hx hxV
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxV
      obtain ⟨k, hnk⟩ := mem_iUnion.mp hn
      apply hx
      exact mem_iUnion.mpr ⟨Nat.pair n k, by simpa [K, Nat.unpair_pair] using hnk⟩
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
    simpa only [mem_compl_iff, not_not] using hx

end HarmonicBalls

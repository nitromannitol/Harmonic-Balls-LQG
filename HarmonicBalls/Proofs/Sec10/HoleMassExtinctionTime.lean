import HarmonicBalls.Proofs.Sec10.HoleExtinctionCoverage
import HarmonicBalls.Proofs.Sec9.WeakUniquenessInclusions

/-! # Hole extinction and remaining mass

For a full-support measure, a surviving open descendant has positive mass.
Together with almost-everywhere coverage before the endpoint, this identifies
the lifetime of a bounded hole with its mass extinction time.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- A nonempty open complementary component contained in `U` witnesses
positive mass outside the closed set, for every full-support measure. -/
theorem measure_sdiff_pos_of_complement_component
    (μ : Measure ℂ) [μ.IsOpenPosMeasure] {F U V : Set ℂ}
    (hF : IsClosed F) (hV : V ∈ connectedComponentsIn Fᶜ) (hVU : V ⊆ U) :
    0 < μ (U \ F) := by
  obtain ⟨x, hx, hxV⟩ := hV
  have hopen : IsOpen V := by rw [← hxV]; exact hF.isOpen_compl.connectedComponentIn
  have hnon : V.Nonempty := ⟨x, hxV ▸ mem_connectedComponentIn hx⟩
  have hsub : V ⊆ U \ F := by
    intro y hy
    exact ⟨hVU hy, (hxV ▸ connectedComponentIn_subset Fᶜ x) hy⟩
  exact (hopen.measure_pos μ hnon).trans_le (measure_mono hsub)

/-- For a full-support measure, a complementary component has a surviving
open descendant exactly when its part outside the later open set has positive
mass, provided the later frontier is null on the component. -/
theorem measure_sdiff_eq_zero_iff_no_descendant
    (μ : Measure ℂ) [μ.IsOpenPosMeasure] {F C U D : Set ℂ}
    (hFC : F ⊆ closure C) (hopen : IsOpen C)
    (hU : U ∈ connectedComponentsIn Fᶜ) (hUD : U ⊆ D)
    (hnull : μ (frontier C ∩ D) = 0) :
    μ (U \ C) = 0 ↔
      ¬ ∃ V ∈ connectedComponentsIn (closure C)ᶜ, V ⊆ U := by
  constructor
  · intro hzero ⟨V, hV, hVU⟩
    have hpos := measure_sdiff_pos_of_complement_component μ isClosed_closure hV hVU
    have hle : μ (U \ closure C) ≤ μ (U \ C) :=
      measure_mono (sdiff_subset_sdiff_right subset_closure)
    rw [hzero] at hle
    exact (not_le_of_gt hpos) hle
  · intro hno
    have hcover := complement_component_subset_of_no_descendant hFC hU hno
    apply measure_mono_null _ hnull
    intro x hx
    refine ⟨?_, hUD hx.1⟩
    rw [hopen.frontier_eq]
    exact ⟨hcover hx.1, hx.2⟩

universe u

/-- Under I2 and 8.2, the hole has positive unswallowed mass at every time
before its lifetime endpoint and zero unswallowed mass at every later time.
If the endpoint cluster is compactly contained, this also holds at the endpoint. -/
theorem ae_cluster_hole_mass_extinction_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s → s < L →
          ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (∀ s : ℝ, L < s →
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (∀ s : ℝ, t ≤ s →
          (μ ω (U \ cluster (μ ω) 1 z s) = 0 ↔
            ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U)) ∧
        (∀ s : ℝ, t ≤ s → s < L → 0 < μ ω (U \ cluster (μ ω) 1 z s)) ∧
        (∀ s : ℝ, L < s → μ ω (U \ cluster (μ ω) 1 z s) = 0) ∧
        (closure (cluster (μ ω) 1 z L) ⊆ ball 0 1 →
          ∀ s : ℝ, t ≤ s →
            (μ ω (U \ cluster (μ ω) 1 z s) = 0 ↔ L ≤ s)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_covered_before_extinction hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hlife hfull hmono hopen hnull
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter, hcover⟩ := hlife t ht z hz hcl U hU hUb
  refine ⟨L, htL, hbefore, hafter, ?_, ?_, ?_, ?_⟩
  · intro s hts
    have hs : 0 < s := ht.trans_le hts
    apply measure_sdiff_eq_zero_iff_no_descendant (μ ω)
      (closure_mono (hmono t s 1 ht hts zero_lt_one z hz))
      (hopen s 1 hs zero_lt_one z hz).1 hU
    · exact bounded_complement_component_subset_unit_ball isClosed_closure
        (hcl.trans ball_subset_closedBall) hU hUb
    · exact hnull s hs z hz
  · intro s hts hsL
    obtain ⟨V, hV, hVU⟩ := hbefore s hts hsL
    have hpos := measure_sdiff_pos_of_complement_component (μ ω) isClosed_closure hV hVU
    exact hpos.trans_le (measure_mono (sdiff_subset_sdiff_right subset_closure))
  · intro s hLs
    have hs : 0 < s := ht.trans (htL.trans hLs)
    have hmono' := hmono t s 1 ht (htL.le.trans hLs.le) zero_lt_one z hz
    have hUL : U ⊆ closure (cluster (μ ω) 1 z s) :=
      complement_component_subset_of_no_descendant (closure_mono hmono') hU (hafter s hLs)
    have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
      bounded_complement_component_subset_unit_ball isClosed_closure
        (hcl.trans ball_subset_closedBall) hU hUb
    apply measure_mono_null _ (hnull s hs z hz)
    intro x hx
    refine ⟨?_, hUdisc hx.1⟩
    rw [(hopen s 1 hs zero_lt_one z hz).1.frontier_eq]
    exact ⟨hUL hx.1, hx.2⟩
  · intro hclL s hts
    constructor
    · intro hzmass
      by_contra hnot
      have hsL : s < L := lt_of_not_ge hnot
      obtain ⟨V, hV, hVU⟩ := hbefore s hts hsL
      have hpos := measure_sdiff_pos_of_complement_component (μ ω) isClosed_closure hV hVU
      have hle : μ ω (U \ closure (cluster (μ ω) 1 z s)) ≤
          μ ω (U \ cluster (μ ω) 1 z s) :=
        measure_mono (sdiff_subset_sdiff_right subset_closure)
      rw [hzmass] at hle
      exact (not_le_of_gt hpos) hle
    · intro hLs
      apply measure_mono_null _ (hcover hclL)
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro hxunion
      obtain ⟨r, hr, hxr⟩ := mem_iUnion₂.mp hxunion
      have hrs : r ≤ s := hr.2.le.trans hLs
      have hrpos : 0 < r := ht.trans_le hr.1
      exact hx.2 (hmono r s 1 hrpos hrs zero_lt_one z hz hxr)

end HarmonicBalls

import HarmonicBalls.Proofs.Sec10.HoleExtinctionMass

/-! # Total remaining mass before a hole's extinction

When the lifetime endpoint is compactly contained, the part of the original
hole outside the current closed cluster has mass at most the remaining time.
This controls all descendant components together. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A subset of a later cluster closure has at most the mass of the cluster
increment, modulo a null later interior frontier. -/
theorem measure_sdiff_cluster_closure_le_of_subset_later_closure
    (μ : Measure ℂ) {z : ℂ} {s L : ℝ} (hs : 0 ≤ s) (hsL : s ≤ L)
    (hopen : IsOpen (cluster μ 1 z s)) (hopenL : IsOpen (cluster μ 1 z L))
    (hmono : cluster μ 1 z s ⊆ cluster μ 1 z L)
    (hmass : μ (cluster μ 1 z s) = ENNReal.ofReal s)
    (hupper : μ (cluster μ 1 z L) ≤ ENNReal.ofReal L)
    (hnull : μ (frontier (cluster μ 1 z L) ∩ ball (0 : ℂ) 1) = 0)
    {U : Set ℂ} (hU : U ⊆ closure (cluster μ 1 z L))
    (hUdisc : U ⊆ ball (0 : ℂ) 1) :
    μ (U \ closure (cluster μ 1 z s)) ≤ ENNReal.ofReal (L - s) := by
  have hincr := measure_cluster_sdiff_le_of_mass_eq μ 1 z hs hsL hopen hmono hmass hupper
  calc
    μ (U \ closure (cluster μ 1 z s)) ≤
        μ ((cluster μ 1 z L \ cluster μ 1 z s) ∪
          (frontier (cluster μ 1 z L) ∩ ball (0 : ℂ) 1)) := by
      apply measure_mono
      intro x hx
      by_cases hxL : x ∈ cluster μ 1 z L
      · exact Or.inl ⟨hxL, fun hxs => hx.2 (subset_closure hxs)⟩
      · right
        refine ⟨?_, hUdisc hx.1⟩
        rw [frontier, hopenL.interior_eq]
        exact ⟨hU hx.1, hxL⟩
    _ ≤ μ (cluster μ 1 z L \ cluster μ 1 z s) +
        μ (frontier (cluster μ 1 z L) ∩ ball (0 : ℂ) 1) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (L - s) := by rw [hnull, add_zero]; exact hincr

/-- Every union of descendant components is contained in the part of the
original hole still outside the current closed cluster. -/
theorem sUnion_descendant_components_subset_sdiff
    {K U : Set ℂ} :
    ⋃₀ {V | V ∈ connectedComponentsIn Kᶜ ∧ V ⊆ U} ⊆ U \ K := by
  intro x hx
  obtain ⟨V, ⟨hV, hVU⟩, hxV⟩ := mem_sUnion.mp hx
  obtain ⟨y, hy, rfl⟩ := hV
  exact ⟨hVU hxV, connectedComponentIn_subset _ _ hxV⟩


/-- A complementary component of a smaller set, minus a larger set, is
exactly the union of its descendant complementary components. -/
theorem sUnion_descendant_components_eq_sdiff
    {K L U : Set ℂ} (hKL : K ⊆ L) (hU : U ∈ connectedComponentsIn Kᶜ) :
    ⋃₀ {V | V ∈ connectedComponentsIn Lᶜ ∧ V ⊆ U} = U \ L := by
  apply Subset.antisymm sUnion_descendant_components_subset_sdiff
  intro x hx
  obtain ⟨y, hy, hyU⟩ := hU
  have hxKy : x ∈ connectedComponentIn Kᶜ y := hyU.symm ▸ hx.1
  have heq : connectedComponentIn Kᶜ x = U := (connectedComponentIn_eq hxKy).symm.trans hyU
  have hsub : connectedComponentIn Lᶜ x ⊆ U :=
    heq ▸ connectedComponentIn_mono x (compl_subset_compl.mpr hKL)
  exact mem_sUnion.mpr ⟨_, ⟨⟨x, hx.2, rfl⟩, hsub⟩, mem_connectedComponentIn hx.2⟩

universe u

/-- Under I2 and 8.2, a bounded hole has a finite lifetime. If the endpoint
cluster is compactly contained, the total mass of the original hole outside
the current closed cluster is at most the remaining lifetime. No existence of
a hole is asserted. -/
theorem ae_cluster_hole_remaining_mass_le_lifetime
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
        (closure (cluster (μ ω) 1 z L) ⊆ ball 0 1 →
          ∀ s : ℝ, t ≤ s → s < L →
          μ ω (U \ closure (cluster (μ ω) 1 z s)) ≤ ENNReal.ofReal (L - s) ∧
          μ ω (⋃₀ {V | V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ ∧
            V ⊆ U}) ≤ ENNReal.ofReal (L - s)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_lifetime_endpoint_mass_deficit hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlife hopen hmono hmass hnull
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter, hend⟩ := hlife t ht z hz hcl U hU hUb
  refine ⟨L, htL, hbefore, hafter, ?_⟩
  intro hclL s hts hsL
  have hs : 0 < s := ht.trans_le hts
  have hL : 0 < L := hs.trans hsL
  have hno : ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z L))ᶜ, V ⊆ U := by
    intro hV
    exact (hend hV).2 hclL
  have hUL : U ⊆ closure (cluster (μ ω) 1 z L) :=
    complement_component_subset_of_no_descendant
      (closure_mono (hmono t L 1 ht htL.le zero_lt_one z hz)) hU hno
  have hcls : closure (cluster (μ ω) 1 z s) ⊆ ball 0 1 :=
    (closure_mono (hmono s L 1 hs hsL.le zero_lt_one z hz)).trans hclL
  have hfront : μ ω (frontier (cluster (μ ω) 1 z s)) = 0 := by
    apply measure_mono_null _ (hnull s hs z hz)
    intro x hx
    exact ⟨hx, hcls (frontier_subset_closure hx)⟩
  have heq := (hmass 1 s zero_lt_one hs z hz).2.2 hcls hfront
  have hUdisc : U ⊆ ball (0 : ℂ) 1 := hUL.trans hclL
  have hbound := measure_sdiff_cluster_closure_le_of_subset_later_closure (μ ω) hs.le hsL.le
    (hopen s 1 hs zero_lt_one z hz).1 (hopen L 1 hL zero_lt_one z hz).1
    (hmono s L 1 hs hsL.le zero_lt_one z hz) heq
    (hmass 1 L zero_lt_one hL z hz).1 (hnull L hL z hz) hUL hUdisc
  exact ⟨hbound, (measure_mono sUnion_descendant_components_subset_sdiff).trans hbound⟩


end HarmonicBalls

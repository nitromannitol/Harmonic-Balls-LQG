import HarmonicBalls.Proofs.Sec10.HoleExtinctionTotalMass

/-! # Almost-everywhere coverage before hole extinction

A bound on the remaining mass and null cluster frontiers show that almost
all of an extinguishing hole is swallowed strictly before its lifetime endpoint.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- If the mass outside a family of open sets is bounded by the
remaining time modulo null frontiers, their union covers `U` almost everywhere
before the endpoint. -/
theorem measure_sdiff_iUnion_eq_zero_of_remaining_mass
    (μ : Measure ℂ) {U : Set ℂ} {C : ℝ → Set ℂ} {t L : ℝ} (htL : t < L)
    (hopen : ∀ s ∈ Ico t L, IsOpen (C s))
    (hnull : ∀ s ∈ Ico t L, μ (frontier (C s)) = 0)
    (hmass : ∀ s ∈ Ico t L, μ (U \ closure (C s)) ≤ ENNReal.ofReal (L - s)) :
    μ (U \ ⋃ s ∈ Ico t L, C s) = 0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let s : ℝ := max t (L - ε)
  have hs : s ∈ Ico t L := by
    constructor
    · exact le_max_left _ _
    · apply max_lt htL
      have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
      linarith
  have hsub : U \ ⋃ s ∈ Ico t L, C s ⊆ (U \ closure (C s)) ∪ frontier (C s) := by
    intro x hx
    have hxC : x ∉ C s := by
      intro hxc
      exact hx.2 (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hs, hxc⟩⟩)
    by_cases hxcl : x ∈ closure (C s)
    · right
      rw [(hopen s hs).frontier_eq]
      exact ⟨hxcl, hxC⟩
    · exact Or.inl ⟨hx.1, hxcl⟩
  calc
    μ (U \ ⋃ s ∈ Ico t L, C s) ≤ μ (U \ closure (C s)) + μ (frontier (C s)) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (L - s) := by rw [hnull s hs, add_zero]; exact hmass s hs
    _ ≤ (ε : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      dsimp [s]
      have := le_max_right t (L - (ε : ℝ))
      linarith
    _ = 0 + ε := by simp

universe u

/-- Under I2 and 8.2, almost all points of any bounded hole are swallowed
before its finite lifetime endpoint, provided that endpoint is compactly
contained in the unit disc. This is simultaneous over poles and holes. -/
theorem ae_cluster_hole_covered_before_extinction
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
          μ ω (U \ ⋃ s ∈ Ico t L, cluster (μ ω) 1 z s) = 0) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_remaining_mass_le_lifetime hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlife hopen hmono hnull
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter, hmass⟩ := hlife t ht z hz hcl U hU hUb
  refine ⟨L, htL, hbefore, hafter, ?_⟩
  intro hclL
  apply measure_sdiff_iUnion_eq_zero_of_remaining_mass (μ ω) htL
  · intro s hs
    exact (hopen s 1 (ht.trans_le hs.1) zero_lt_one z hz).1
  · intro s hs
    have hcls : closure (cluster (μ ω) 1 z s) ⊆ ball 0 1 :=
      (closure_mono (hmono s L 1 (ht.trans_le hs.1) hs.2.le zero_lt_one z hz)).trans hclL
    apply measure_mono_null _ (hnull s (ht.trans_le hs.1) z hz)
    intro x hx
    exact ⟨hx, hcls (frontier_subset_closure hx)⟩
  · intro s hs
    exact (hmass hclL s hs.1 hs.2).1

end HarmonicBalls

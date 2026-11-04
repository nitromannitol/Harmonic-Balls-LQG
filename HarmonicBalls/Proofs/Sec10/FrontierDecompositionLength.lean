import HarmonicBalls.Proofs.Sec10.FrontierDecompositionDimension

/-! # Length of essential pieces of a complementary frontier

A proper closed decomposition of a frontier contains a relatively open
piece on each side. The local frontier length bound gives each piece positive
one-dimensional Hausdorff measure. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal MeasureTheory

/-- A proper closed cover has two essential pieces of positive Hausdorff
length when the covered set has positive local length at every point. -/
theorem closed_cover_essential_parts_positive_length
    {S A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = S)
    (hproperA : ∃ x ∈ S, x ∉ A) (hproperB : ∃ x ∈ S, x ∉ B)
    (hlocal : ∀ p ∈ S, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      ENNReal.ofReal r ≤ μH[1] (S ∩ ball p r)) :
    0 < μH[1] (A \ B) ∧ 0 < μH[1] (B \ A) := by
  have hone : ∀ {A B : Set ℂ}, IsClosed B → A ∪ B = S →
      (∃ x ∈ S, x ∉ B) → 0 < μH[1] (A \ B) := by
    intro A B hB hcover hproper
    obtain ⟨p, hpS, hpB⟩ := hproper
    obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hpB)
    obtain ⟨R, hR, hlen⟩ := hlocal p hpS
    let r := min δ R / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrδ : r ≤ δ := by dsimp [r]; linarith [min_le_left δ R]
    have hrR : r ≤ R := by dsimp [r]; linarith [min_le_right δ R]
    have hsub : S ∩ ball p r ⊆ A \ B := by
      intro q hq
      have hqB : q ∉ B := hδB (ball_subset_ball hrδ hq.2)
      have hqAB : q ∈ A ∪ B := hcover.symm ▸ hq.1
      exact ⟨hqAB.resolve_right hqB, hqB⟩
    exact (ENNReal.ofReal_pos.mpr hr).trans_le ((hlen r hr hrR).trans (measure_mono hsub))
  exact ⟨hone hB hcover hproperB, hone hA (by simpa [union_comm] using hcover) hproperA⟩

universe u

/-- Under volume growth, both essential pieces of every proper closed
cover of every compact-cluster complementary frontier have positive length. -/
theorem ae_cluster_frontier_closed_cover_essential_parts_positive_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ A B : Set ℂ, IsClosed A → IsClosed B → A ∪ B = frontier U →
      (∃ x ∈ frontier U, x ∉ A) → (∃ x ∈ frontier U, x ∉ B) →
      0 < μH[1] (A \ B) ∧ 0 < μH[1] (B \ A) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_complement_frontier_local_length hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ] with ω hlocal
  intro t ht z hz hcl U hU A B hA hB hcover hproperA hproperB
  exact closed_cover_essential_parts_positive_length hA hB hcover hproperA hproperB
    (hlocal t ht z hz hcl U hU)

/-- A hypothetical cut point yields nonseparating compact pieces whose
essential parts both have positive length. This does not assert that such a
cut point exists. -/
theorem ae_cluster_cut_point_yields_nonseparating_pieces_positive_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ x ∈ cluster (μ ω) 1 z t, ∀ y ∈ U, ∀ a ∈ frontier U,
      ¬ IsPreconnected (frontier U \ {a}) →
      ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ A ∪ B = frontier U ∧
        A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
        y ∈ connectedComponentIn Bᶜ x ∧
        y ∉ connectedComponentIn (A ∪ B)ᶜ x ∧
        0 < μH[1] (A \ B) ∧ 0 < μH[1] (B \ A) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_cut_point_separation_obstruction hI2 γ hγ hγ2 α₀ hα
      Ω P hC hcirc μ hGFF hμ,
    ae_cluster_frontier_closed_cover_essential_parts_positive_length hI2 γ hγ hγ2 α₀ hα
      Ω P hC hcirc μ hGFF hμ] with ω hsep hlength
  intro t ht z hz hcl U hU x hx y hy a ha hcut
  obtain ⟨A, B, hA, hB, hcover, hint, hAx, hBx, hABx⟩ :=
    hsep t ht z hz hcl U hU x hx y hy a ha hcut
  have hAp : ∃ p ∈ frontier U, p ∉ A := by
    apply not_subset.mp
    intro hsub
    have hAs : A ⊆ frontier U := by rw [← hcover]; exact subset_union_left
    have heq : A = frontier U := Subset.antisymm hAs hsub
    apply hABx
    simpa only [hcover, ← heq] using hAx
  have hBp : ∃ p ∈ frontier U, p ∉ B := by
    apply not_subset.mp
    intro hsub
    have hBs : B ⊆ frontier U := by rw [← hcover]; exact subset_union_right
    have heq : B = frontier U := Subset.antisymm hBs hsub
    apply hABx
    simpa only [hcover, ← heq] using hBx
  exact ⟨A, B, hA, hB, hcover, hint, hAx, hBx, hABx,
    hlength t ht z hz hcl U hU A B hA.isClosed hB.isClosed hcover hAp hBp⟩

end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.AccumulatingPointRemoval
import HarmonicBalls.Proofs.Sec5.FinitePunctureCompetitors

/-! # Finite barrier covers near locally finite accumulation sets -/

namespace HarmonicBalls

open Metric Set Filter Topology

/-- Outside a neighbourhood of the possible accumulation points, only finitely
many deleted points can lie in a compact subset of the domain. -/
theorem finite_inter_compact_sdiff_neighborhood_of_locally_finite_accumulation
    {U K L C W : Set ℂ} (hC : IsCompact C) (hCU : C ⊆ U)
    (hW : IsOpen W) (hLW : L ∩ C ⊆ W)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ U \ L → (K ∩ D).Finite) :
    (K ∩ (C \ W)).Finite := by
  apply hK (C \ W) (hC.diff hW)
  intro x hx
  exact ⟨hCU hx.1, fun hxL => hx.2 (hLW ⟨hxL, hx.1⟩)⟩

/-- A finite sum of capped Green barriers can be made arbitrarily small at a
point outside its poles while exceeding a prescribed level near every pole. -/
theorem exists_finset_cappedGreenBarrier_neighborhood
    {R M ε : ℝ} {x : ℂ} (J : Finset ℂ)
    (hJ : (J : Set ℂ) ⊆ ball (0 : ℂ) R) (hx : x ∉ J)
    (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ c > 0, ∃ W : Set ℂ, IsOpen W ∧ (J : Set ℂ) ⊆ W ∧
      (∑ a ∈ J, cappedGreenBarrier R a c (M + 1) x) < ε ∧
      ∀ y ∈ W, M < ∑ a ∈ J, cappedGreenBarrier R a c (M + 1) y := by
  classical
  have hlim : Tendsto (fun c : ℝ => ∑ a ∈ J,
      cappedGreenBarrier R a c (M + 1) x) (𝓝[>] 0) (𝓝 0) := by
    have hs := tendsto_finsetSum J (fun a ha =>
      tendsto_cappedGreenBarrier_coefficient_zero (R := R)
        (show x ≠ a from fun h => hx (h ▸ ha)) (show 0 ≤ M + 1 by linarith))
    simpa using hs
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), 0 < c ∧
      (∑ a ∈ J, cappedGreenBarrier R a c (M + 1) x) < ε := by
    filter_upwards [self_mem_nhdsWithin, hlim.eventually (eventually_lt_nhds hε)] with c hc hs
    exact ⟨hc, hs⟩
  obtain ⟨c, hc, hsmall⟩ := hev.exists
  let f : ℂ → ℝ := fun y => ∑ a ∈ J, cappedGreenBarrier R a c (M + 1) y
  let W := ball (0 : ℂ) R ∩ f ⁻¹' Ioi M
  have hfc : ContinuousOn f (ball (0 : ℂ) R) := by
    apply continuousOn_finsetSum
    intro a ha
    exact (continuousOn_cappedGreenBarrier (hJ ha) hc).mono ball_subset_closedBall
  have hWo : IsOpen W := hfc.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  refine ⟨c, hc, W, hWo, ?_, hsmall, ?_⟩
  · intro a ha
    refine ⟨hJ ha, ?_⟩
    change M < ∑ b ∈ J, cappedGreenBarrier R b c (M + 1) a
    have hsum : cappedGreenBarrier R a c (M + 1) a ≤
        ∑ b ∈ J, cappedGreenBarrier R b c (M + 1) a :=
      Finset.single_le_sum (f := fun b => cappedGreenBarrier R b c (M + 1) a)
        (fun b _ => cappedGreenBarrier_nonneg hc.le (show 0 ≤ M + 1 by linarith)) ha
    have heq : cappedGreenBarrier R a c (M + 1) a = M + 1 := by
      simp [cappedGreenBarrier]
    rw [heq] at hsum
    linarith
  · intro y hy
    exact hy.2

/-- A compact part of a deletion with locally finite accumulation admits a
finite capped Green barrier cover that is arbitrarily small at a prescribed
point outside the deletion and its accumulation set. -/
theorem exists_cappedGreenBarrier_cover_of_locally_finite_accumulation
    {R M ε : ℝ} {K L C : Set ℂ} {x : ℂ}
    (hC : IsCompact C) (hCU : C ⊆ ball (0 : ℂ) R)
    (hL : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R → (L ∩ D).Finite)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ ball (0 : ℂ) R \ L → (K ∩ D).Finite)
    (hxK : x ∉ K) (hxL : x ∉ L) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ (J₁ J₂ : Finset ℂ) (c₁ c₂ : ℝ),
      (J₁ : Set ℂ) ⊆ ball (0 : ℂ) R ∧ (J₂ : Set ℂ) ⊆ ball (0 : ℂ) R ∧
      0 < c₁ ∧ 0 < c₂ ∧
      (∑ a ∈ J₁, cappedGreenBarrier R a c₁ (M + 1) x) +
        (∑ a ∈ J₂, cappedGreenBarrier R a c₂ (M + 1) x) < ε ∧
      ∀ y ∈ K ∩ C, M <
        (∑ a ∈ J₁, cappedGreenBarrier R a c₁ (M + 1) y) +
        (∑ a ∈ J₂, cappedGreenBarrier R a c₂ (M + 1) y) := by
  classical
  let J₁ : Finset ℂ := (hL C hC hCU).toFinset
  have hJ₁ : (J₁ : Set ℂ) = L ∩ C := Set.Finite.coe_toFinset _
  have hJ₁U : (J₁ : Set ℂ) ⊆ ball (0 : ℂ) R := by
    rw [hJ₁]
    exact inter_subset_right.trans hCU
  have hxJ₁ : x ∉ J₁ := by
    intro h
    have h' : x ∈ (J₁ : Set ℂ) := h
    rw [hJ₁] at h'
    exact hxL h'.1
  obtain ⟨c₁, hc₁, W₁, hW₁, hJ₁W, hsmall₁, hcover₁⟩ :=
    exists_finset_cappedGreenBarrier_neighborhood J₁ hJ₁U hxJ₁ hM (half_pos hε)
  have hLW : L ∩ C ⊆ W₁ := by simpa only [hJ₁] using hJ₁W
  let J₂ : Finset ℂ :=
    (finite_inter_compact_sdiff_neighborhood_of_locally_finite_accumulation
      hC hCU hW₁ hLW hK).toFinset
  have hJ₂ : (J₂ : Set ℂ) = K ∩ (C \ W₁) := Set.Finite.coe_toFinset _
  have hJ₂U : (J₂ : Set ℂ) ⊆ ball (0 : ℂ) R := by
    rw [hJ₂]
    exact inter_subset_right.trans (sdiff_subset.trans hCU)
  have hxJ₂ : x ∉ J₂ := by
    intro h
    have h' : x ∈ (J₂ : Set ℂ) := h
    rw [hJ₂] at h'
    exact hxK h'.1
  obtain ⟨c₂, hc₂, W₂, hW₂, hJ₂W, hsmall₂, hcover₂⟩ :=
    exists_finset_cappedGreenBarrier_neighborhood J₂ hJ₂U hxJ₂ hM (half_pos hε)
  refine ⟨J₁, J₂, c₁, c₂, hJ₁U, hJ₂U, hc₁, hc₂, by linarith, ?_⟩
  intro y hy
  have hn₁ : 0 ≤ ∑ a ∈ J₁, cappedGreenBarrier R a c₁ (M + 1) y :=
    Finset.sum_nonneg fun a _ => cappedGreenBarrier_nonneg hc₁.le (by linarith)
  have hn₂ : 0 ≤ ∑ a ∈ J₂, cappedGreenBarrier R a c₂ (M + 1) y :=
    Finset.sum_nonneg fun a _ => cappedGreenBarrier_nonneg hc₂.le (by linarith)
  by_cases hyW : y ∈ W₁
  · linarith [hcover₁ y hyW]
  · have hyJ : y ∈ J₂ := by
      change y ∈ (J₂ : Set ℂ)
      rw [hJ₂]
      exact ⟨hy.1, hy.2, hyW⟩
    linarith [hcover₂ y (hJ₂W hyJ)]

#print axioms exists_cappedGreenBarrier_cover_of_locally_finite_accumulation
#print axioms finite_inter_compact_sdiff_neighborhood_of_locally_finite_accumulation
#print axioms exists_finset_cappedGreenBarrier_neighborhood

end HarmonicBalls

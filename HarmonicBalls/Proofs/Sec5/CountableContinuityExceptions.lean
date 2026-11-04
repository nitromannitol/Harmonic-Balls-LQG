import HarmonicBalls.Proofs.Sec5.BoundaryContinuityCompactness
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import Mathlib.Topology.Order.Monotone

/-! # Countably many possible right-continuity exceptions

For a monotone family contained in a fixed compact disc, right continuity of
closed clusters can fail at only countably many positive times. This result
also applies when clusters meet the disc boundary; it does not rule out an
exception at a specified time.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Pointwise

/-- A monotone family of subsets of the unit disc is right-continuous in the
one-sided Hausdorff sense outside a countable set of positive times. -/
theorem countable_not_rightContinuous_of_monotone
    {F : ℝ → Set ℂ}
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1) :
    {t : ℝ | 0 < t ∧ ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (F s) ⊆ F t + ball (0 : ℂ) ε}.Countable := by
  classical
  let B := countableBasis ℂ
  let f : B → ℝ → ℝ := fun U t => if Disjoint (U : Set ℂ) (closure (F t)) then 0 else 1
  have hf (U : B) : MonotoneOn (f U) (Ioi 0) := by
    intro s hs t ht hst
    have hsub : closure (F s) ⊆ closure (F t) := closure_mono (hmono s t hs hst)
    dsimp only [f]
    by_cases h1 : Disjoint (U : Set ℂ) (closure (F s))
    · simp only [ite_eq_left h1, zero_le_one, le_refl, ite_nonneg]
    · have h2 : ¬ Disjoint (U : Set ℂ) (closure (F t)) :=
        fun h => h1 (h.mono_right hsub)
      simp only [ite_eq_right h1, ite_eq_right h2, le_refl]
  let E : B → Set ℝ := fun U => {t ∈ Ioi 0 | ¬ ContinuousWithinAt (f U) (Ioi 0 ∩ Ioi t) t}
  have hE : ∀ U, (E U).Countable := fun U => (hf U).countable_not_continuousWithinAt_Ioi
  apply (Set.countable_iUnion hE).mono
  intro t ht
  obtain ⟨ht, hfail⟩ := ht
  have hnot : ¬ (⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))) ⊆ closure (F t) := by
    intro hsub
    exact hfail ((closure_dyadic_iInter_subset_iff_right_continuous ht hmono hbound).mp hsub)
  obtain ⟨x, hx, hxt⟩ := Set.not_subset.mp hnot
  obtain ⟨U, hUB, hxU, hUsub⟩ := (isBasis_countableBasis ℂ).exists_subset_of_mem_open
    (show x ∈ (closure (F t))ᶜ from hxt) isClosed_closure.isOpen_compl
  let U' : B := ⟨U, hUB⟩
  have hdis : Disjoint U (closure (F t)) := Set.disjoint_left.mpr (fun y hy hy' => hUsub hy hy')
  have hft : f U' t = 0 := by
    change (if Disjoint U (closure (F t)) then (0 : ℝ) else 1) = 0
    rw [ite_eq_left hdis]
  have hfuture (n : ℕ) : f U' (t + (2 : ℝ)⁻¹ ^ n) = 1 := by
    have hnd : ¬ Disjoint U (closure (F (t + (2 : ℝ)⁻¹ ^ n))) := by
      intro hd
      exact Set.disjoint_left.mp hd hxU (Set.mem_iInter.mp hx n)
    change (if Disjoint U (closure (F (t + (2 : ℝ)⁻¹ ^ n))) then (0 : ℝ) else 1) = 1
    rw [ite_eq_right hnd]
  apply Set.mem_iUnion.mpr
  refine ⟨U', ht, ?_⟩
  intro hcont
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp hcont 1 (by norm_num)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hp : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  have hnear : dist (t + (2 : ℝ)⁻¹ ^ n) t < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hp]
    exact hn
  have hmem : t + (2 : ℝ)⁻¹ ^ n ∈ Ioi (0 : ℝ) ∩ Ioi t := by
    simp only [mem_inter_iff, mem_Ioi]
    exact ⟨add_pos ht hp, lt_add_of_pos_right t hp⟩
  have hval := hδ' hmem hnear
  rw [hfuture, hft] at hval
  norm_num at hval

universe u

/-- For all centres simultaneously, the possible exceptional times of a
unit-disc LQG cluster form a countable set. Volume growth supplies the cluster
monotonicity used in this conclusion. -/
theorem ae_countable_cluster_rightContinuity_exceptions
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      {t : ℝ | 0 < t ∧ ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε}.Countable := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro z hz
  exact countable_not_rightContinuous_of_monotone
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball)

/-- For every centre simultaneously, the closed clusters satisfy the dyadic
right-intersection identity for Lebesgue-almost every positive time. -/
theorem ae_cluster_dyadic_inter_eq_ae_time
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ᵐ t ∂volume, 0 < t →
      (⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + (2 : ℝ)⁻¹ ^ n))) =
        closure (cluster (μ ω) 1 z t) := by
  filter_upwards [ae_countable_cluster_rightContinuity_exceptions hI2 hγ hγ2 hα hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount hmono
  intro z hz
  filter_upwards [(hcount z hz).ae_notMem volume] with t hnot ht
  have hc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
        cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
    by_contra hfail
    exact hnot ⟨ht, hfail⟩
  exact (cluster_closure_dyadic_iInter_eq_iff_right_continuous ht
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)).mpr hc

end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.FiniteLargeDiscontinuities
import Mathlib.Data.Set.Card.Arithmetic

/-! # A uniform packing bound for large continuity failures -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise BigOperators

/-- At a fixed tolerance, one finite bound works for all monotone families
contained in the unit disc. -/
theorem exists_uniform_encard_large_right_continuity_failures (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ C : ℝ → Set ℂ,
      (∀ a b, 0 < a → a ≤ b → C a ⊆ C b) →
      (∀ s, 0 < s → C s ⊆ ball (0 : ℂ) 1) →
      {t : ℝ | 0 < t ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (C s) ⊆ C t + ball (0 : ℂ) ε}.encard ≤ N := by
  classical
  let d := ε / 2
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨K, _hKsub, hKfin, hcover⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).finite_cover_balls (show 0 < d / 4 by positivity)
  refine ⟨hKfin.toFinset.card, ?_⟩
  intro C hmono hbound
  let J : ℂ → Set ℝ := fun y => {t | 0 < t ∧
    Disjoint (ball y (d / 2)) (closure (C t)) ∧
    ∀ n : ℕ, (ball y (d / 2) ∩ closure (C (t + dyadicScale n))).Nonempty}
  have hJ (y : ℂ) : (J y).Subsingleton := by
    intro a ha b hb
    have hnot (a b : ℝ) (ha : a ∈ J y) (hb : b ∈ J y) (hab : a < b) : False := by
      have hgap : 0 < b - a := sub_pos.mpr hab
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (2 : ℝ)⁻¹ < 1)
      obtain ⟨x, hxy, hx⟩ := ha.2.2 n
      have hs : 0 < a + dyadicScale n := add_pos ha.1 (dyadicScale_pos n)
      have hst : a + dyadicScale n ≤ b := by
        dsimp [dyadicScale]
        linarith
      have hxb : x ∈ closure (C b) := closure_mono (hmono _ _ hs hst) hx
      exact Set.disjoint_left.mp hb.2.1 hxy hxb
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (hnot a b ha hb hab).elim
    · exact hab
    · exact (hnot b a hb ha hab).elim
  have hsubset : {t : ℝ | 0 < t ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (C s) ⊆ C t + ball (0 : ℂ) ε} ⊆ ⋃ y ∈ K, J y := by
    intro t ht
    have htpos := ht.1
    have hfail : ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (C s) ⊆ C t + ball (0 : ℂ) (2 * d) := by
      have hd2 : 2 * d = ε := by dsimp [d]; ring
      simpa only [hd2] using ht.2
    obtain ⟨x, hx, hsep⟩ := exists_separated_future_point_of_not_uniform_right_continuity
      C t d htpos hd hmono hbound hfail
    have hxcl : x ∈ closedBall (0 : ℂ) 1 := by
      apply closure_minimal (hbound _ (add_pos htpos (dyadicScale_pos 0)) |>.trans ball_subset_closedBall)
        isClosed_closedBall
      exact Set.mem_iInter.mp hx 0
    obtain ⟨y, hyK, hxy⟩ := Set.mem_iUnion.mp (hcover hxcl) |>.imp fun _ h => Set.mem_iUnion.mp h
    have hyx : dist x y < d / 4 := by simpa [mem_ball] using hxy
    have hxball : x ∈ ball y (d / 2) := by
      rw [mem_ball]
      linarith
    have hdis : Disjoint (ball y (d / 2)) (closure (C t)) := by
      apply Set.disjoint_left.mpr
      intro w hwy hwcl
      apply hsep _ hwcl
      rw [mem_ball]
      have htri := dist_triangle w y x
      have hwy' := mem_ball.mp hwy
      rw [dist_comm y x] at htri
      linarith
    refine Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyK, ?_⟩⟩
    refine ⟨htpos, hdis, ?_⟩
    intro n
    exact ⟨x, hxball, Set.mem_iInter.mp hx n⟩
  calc
    _ ≤ (⋃ y ∈ K, J y).encard := Set.encard_mono hsubset
    _ = (⋃ y ∈ hKfin.toFinset, J y).encard := by simp
    _ ≤ ∑ y ∈ hKfin.toFinset, (J y).encard := hKfin.toFinset.set_encard_biUnion_le J
    _ ≤ ∑ _y ∈ hKfin.toFinset, (1 : ℕ∞) := by
      apply Finset.sum_le_sum
      intro y hy
      exact Set.encard_le_one_iff_subsingleton.mpr (hJ y)
    _ = ↑hKfin.toFinset.card := by simp

universe u

/-- At each tolerance, a deterministic bound controls the number of
right-continuity failures at every centre of the unit disc almost surely. -/
theorem exists_uniform_encard_lqg_right_continuity_failures
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      {t : ℝ | 0 < t ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε}.encard ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_encard_large_right_continuity_failures ε hε
  refine ⟨N, ?_⟩
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro z hz
  exact hN (fun t => cluster (μ ω) 1 z t)
    (fun a b ha hab => hmono a b 1 ha hab zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball)

/-- One deterministic function bounds the counts simultaneously for every
positive tolerance and every centre, on a single almost-sure event. -/
theorem exists_uniform_count_lqg_right_continuity_failures
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ N : ℝ → ℕ, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z ∈ ball (0 : ℂ) 1,
      {t : ℝ | 0 < t ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε}.encard ≤ N ε := by
  classical
  have hbound : ∀ ε : ℝ, ∃ N : ℕ, 0 < ε → ∀ C : ℝ → Set ℂ,
      (∀ a b, 0 < a → a ≤ b → C a ⊆ C b) →
      (∀ s, 0 < s → C s ⊆ ball (0 : ℂ) 1) →
      {t : ℝ | 0 < t ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (C s) ⊆ C t + ball (0 : ℂ) ε}.encard ≤ N := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨N, hN⟩ := exists_uniform_encard_large_right_continuity_failures ε hε
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => (hε h).elim⟩
  choose N hN using hbound
  refine ⟨N, ?_⟩
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro ε hε z hz
  exact hN ε hε (fun t => cluster (μ ω) 1 z t)
    (fun a b ha hab => hmono a b 1 ha hab zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball)

end HarmonicBalls


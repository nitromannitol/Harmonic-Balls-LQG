import HarmonicBalls.Draft.Section10

/-!
# Counting crossing components by mass

The last step of Lemma 10.1 bounds the number of disjoint crossing
components once each carries a fixed fraction of the mass of a common annulus.
This file proves that deterministic measure-theoretic step.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal

/-- A finite disjoint family of measurable subsets, each carrying at least an
`α`-fraction of the mass of `A`, has at most `⌈1 / α⌉` members. -/
theorem card_le_ceil_inv_of_disjoint_mass
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X)
    (hApos : μ A ≠ 0) (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α)
    (s : Finset ι) (F : ι → Set X)
    (hFmeas : ∀ i ∈ s, MeasurableSet (F i))
    (hFsub : ∀ i ∈ s, F i ⊆ A)
    (hFdisj : Set.PairwiseDisjoint (↑s : Set ι) F)
    (hFmass : ∀ i ∈ s, ENNReal.ofReal α * μ A ≤ μ (F i)) :
    s.card ≤ ⌈1 / α⌉₊ := by
  classical
  have hsum : (∑ i ∈ s, μ (F i)) ≤ μ A := by
    rw [← measure_biUnion_finset hFdisj hFmeas]
    exact measure_mono (iUnion₂_subset hFsub)
  have hFi : ∀ i ∈ s, μ (F i) ≠ ∞ := by
    intro i hi
    exact ne_top_of_le_ne_top hAfin (measure_mono (hFsub i hi))
  have hsumR : (∑ i ∈ s, (μ (F i)).toReal) ≤ (μ A).toReal := by
    have := ENNReal.toReal_mono hAfin hsum
    rwa [ENNReal.toReal_sum hFi] at this
  have hbound : ∀ i ∈ s, α * (μ A).toReal ≤ (μ (F i)).toReal := by
    intro i hi
    have := ENNReal.toReal_mono (hFi i hi) (hFmass i hi)
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le] using this
  have hsumlower := Finset.sum_le_sum hbound
  simp only [Finset.sum_const, nsmul_eq_mul] at hsumlower
  have hpos : 0 < (μ A).toReal := ENNReal.toReal_pos hApos hAfin
  have hratio : (s.card : ℝ) ≤ 1 / α := by
    apply (le_div_iff₀ hα).2
    nlinarith
  have hc : (s.card : ℝ) ≤ (⌈1 / α⌉₊ : ℝ) := hratio.trans (Nat.le_ceil _)
  exact_mod_cast hc

/-- The same mass bound for an arbitrary, possibly infinite, family. -/
theorem encard_le_ceil_inv_of_disjoint_mass
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X)
    (hApos : μ A ≠ 0) (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α)
    (S : Set ι) (F : ι → Set X)
    (hFmeas : ∀ i ∈ S, MeasurableSet (F i))
    (hFsub : ∀ i ∈ S, F i ⊆ A)
    (hFdisj : Set.PairwiseDisjoint S F)
    (hFmass : ∀ i ∈ S, ENNReal.ofReal α * μ A ≤ μ (F i)) :
    S.encard ≤ ⌈1 / α⌉₊ := by
  classical
  have hcard : ∀ s : Finset ι, (↑s : Set ι) ⊆ S → s.card ≤ ⌈1 / α⌉₊ := by
    intro s hs
    exact card_le_ceil_inv_of_disjoint_mass μ A hApos hAfin hα s F
      (fun i hi => hFmeas i (hs hi)) (fun i hi => hFsub i (hs hi))
      (fun i hi j hj hij => hFdisj (hs hi) (hs hj) hij) (fun i hi => hFmass i (hs hi))
  have hfinite : S.Finite := by
    by_contra h
    obtain ⟨s, hs, hc⟩ := (show S.Infinite from h).exists_subset_card_eq (⌈1 / α⌉₊ + 1)
    have := hcard s hs
    omega
  rw [hfinite.encard_eq_coe_toFinset_card]
  exact_mod_cast hcard hfinite.toFinset (by simp)

/-- Distinct connected components of a set are disjoint. -/
theorem pairwiseDisjoint_connectedComponentsIn {X : Type*} [TopologicalSpace X]
    (F : Set X) : Set.PairwiseDisjoint (connectedComponentsIn F) id := by
  intro C hC D hD hne
  obtain ⟨x, hx, rfl⟩ := hC
  obtain ⟨y, hy, rfl⟩ := hD
  change Disjoint (connectedComponentIn F x) (connectedComponentIn F y)
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  exact hne ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm)

/-- If each crossing component has more than an `α`-fraction of the mass of
`A`, then there are at most `⌈1 / α⌉` crossing components. The conclusion
also holds when `A` has zero mass. -/
theorem encard_crossingComponents_le_ceil_inv
    (μ : Measure ℂ) (Λ A : Set ℂ) (hΛ : IsOpen Λ) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α) (w : ℂ) (r s : ℝ)
    (hmass : ∀ C ∈ crossingComponents (Λ ∩ ball w s) w r s,
      ENNReal.ofReal α * μ A < μ (C ∩ A)) :
    (crossingComponents (Λ ∩ ball w s) w r s).encard ≤ ⌈1 / α⌉₊ := by
  classical
  let S := crossingComponents (Λ ∩ ball w s) w r s
  change S.encard ≤ ⌈1 / α⌉₊
  by_cases hzero : μ A = 0
  · have hS : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      have hle : μ (C ∩ A) ≤ μ A := measure_mono inter_subset_right
      have := hmass C hC
      rw [hzero] at hle this
      simp only [mul_zero] at this
      exact (not_lt_of_ge hle) this
    simp [hS]
  · apply encard_le_ceil_inv_of_disjoint_mass μ A hzero hAfin hα S (fun C => C ∩ A)
    · intro C hC
      obtain ⟨⟨x, hx, rfl⟩, _⟩ := hC
      exact ((hΛ.inter isOpen_ball).connectedComponentIn.measurableSet).inter hA
    · intro C hC
      exact inter_subset_right
    · intro C hC D hD hne
      have hd := pairwiseDisjoint_connectedComponentsIn (Λ ∩ ball w s) hC.1 hD.1 hne
      exact hd.mono inter_subset_left inter_subset_left
    · intro C hC
      exact (hmass C hC).le

/-- A Harnack-type component estimate bounds crossings of a smaller inner
circle: closure contact with that circle gives a point in the test ball. -/
theorem encard_crossingComponents_of_mass_or_avoids
    (μ : Measure ℂ) (Λ A : Set ℂ) (hΛ : IsOpen Λ) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α) (w : ℂ) (r q s : ℝ) (hrq : r < q)
    (hcomponent : ∀ C ∈ connectedComponentsIn (Λ ∩ ball w s),
      μ (C ∩ A) ≤ ENNReal.ofReal α * μ A → C ∩ closedBall w q = ∅) :
    (crossingComponents (Λ ∩ ball w s) w r s).encard ≤ ⌈1 / α⌉₊ := by
  apply encard_crossingComponents_le_ceil_inv μ Λ A hΛ hA hAfin hα w r s
  intro C hC
  apply lt_of_not_ge
  intro hsmall
  obtain ⟨x, hxcl, hxsphere⟩ := hC.2.1
  have hxball : x ∈ ball w q := mem_ball.mpr ((mem_sphere.mp hxsphere).trans_lt hrq)
  obtain ⟨y, hyball, hyC⟩ := mem_closure_iff.mp hxcl _ isOpen_ball hxball
  have hy : y ∈ C ∩ closedBall w q := ⟨hyC, ball_subset_closedBall hyball⟩
  rw [hcomponent C hC.1 hsmall] at hy
  exact hy

end HarmonicBalls

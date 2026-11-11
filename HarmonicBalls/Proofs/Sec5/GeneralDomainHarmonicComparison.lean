import HarmonicBalls.Proofs.Sec5.GeneralDomainDeletionComparison

/-! # Local harmonic comparison across a thin deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- Capped barriers remove a locally finite-rank closed set from harmonic
comparison on a disc with arbitrary centre. -/
theorem harmonic_sub_le_of_locallyFiniteRankOn_ball
    {R r C M : ℝ} {c x : ℂ} {K : Set ℂ} {h q : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R) (hKclosed : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hh : HarmonicOnNhd h (closedBall c r \ K))
    (hq : HarmonicOnNhd q (closedBall c r)) (hM : 0 ≤ M)
    (hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, h y - q y ≤ C + M)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y - q y ≤ C)
    (hx : x ∈ ball c r \ K) : h x - q x ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hbc, hbΔ, hbn, hbx, hbar⟩ :=
    exists_capped_barrier_of_locallyFiniteRankOn hKclosed hK
      (isCompact_closedBall _ _) hball hx.2 hM hε
  have hbc' : ContinuousOn b (closedBall c r) := hbc.mono (hball.trans ball_subset_closedBall)
  have hDopen : IsOpen (ball c r \ K) := isOpen_ball.sdiff hKclosed
  have hDR : ball c r \ K ⊆ ball (0 : ℂ) R :=
    sdiff_subset.trans (ball_subset_closedBall.trans hball)
  have hbs : IsSuperharmonicOn (ball c r \ K) b :=
    superharmonicOfLaplacianLEStep_holds _ b hDopen
      (hbc'.mono (sdiff_subset.trans ball_subset_closedBall)) (hbΔ.mono_set hDR)
  have hcmp := harmonic_sub_le_of_superharmonic_barrier hKclosed hh hq hbc' hbs hnear
    hbar (fun y _ => hbn y) hbd x hx
  linarith

/-- A bounded harmonic function with zero boundary values on a punctured disc
vanishes there, even when the deleted set has locally finite accumulation rank. -/
theorem harmonicOnNhd_eq_zero_of_locallyFiniteRankOn_ball
    {R r M : ℝ} {c : ℂ} {K : Set ℂ} {h : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R) (hKclosed : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hh : HarmonicOnNhd h (closedBall c r \ K)) (hM : 0 ≤ M)
    (hbound : ∀ y ∈ ball c r \ K, |h y| ≤ M)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y = 0)
    {x : ℂ} (hx : x ∈ ball c r \ K) : h x = 0 := by
  have hle : h x ≤ 0 := by
    have hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, h y - 0 ≤ 0 + M := by
      intro a ha
      filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using (le_abs_self (h y)).trans (hbound y hy)
    have hb : ∀ y ∈ sphere c r, y ∉ K → h y - 0 ≤ 0 := by
      intro y hy hyK
      simp [hbd y hy hyK]
    simpa using harmonic_sub_le_of_locallyFiniteRankOn_ball hball hKclosed hK hh
      (harmonicOnNhd_const 0) hM hnear hb hx
  have hge : 0 ≤ h x := by
    have hnear : ∀ a ∈ K, ∀ᶠ y in 𝓝[ball c r \ K] a, (-h) y - 0 ≤ 0 + M := by
      intro a ha
      filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using (neg_le_abs (h y)).trans (hbound y hy)
    have hb : ∀ y ∈ sphere c r, y ∉ K → (-h) y - 0 ≤ 0 := by
      intro y hy hyK
      simp [hbd y hy hyK]
    have ht := harmonic_sub_le_of_locallyFiniteRankOn_ball hball hKclosed hK hh.neg
      (harmonicOnNhd_const 0) hM hnear hb hx
    simpa using ht
  exact le_antisymm hle hge

/-- A bounded harmonic function on the punctured disc agrees with its
harmonic replacement whenever they have the same undeleted boundary values. -/
theorem harmonicOnNhd_eq_of_locallyFiniteRankOn_ball
    {R r M : ℝ} {c : ℂ} {K : Set ℂ} {h q : ℂ → ℝ}
    (hball : closedBall c r ⊆ ball (0 : ℂ) R) (hKclosed : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hh : HarmonicOnNhd h (closedBall c r \ K))
    (hq : HarmonicOnNhd q (closedBall c r)) (hM : 0 ≤ M)
    (hbound : ∀ y ∈ ball c r \ K, |h y - q y| ≤ M)
    (hbd : ∀ y ∈ sphere c r, y ∉ K → h y = q y)
    {x : ℂ} (hx : x ∈ ball c r \ K) : h x = q x := by
  have heq := harmonicOnNhd_eq_zero_of_locallyFiniteRankOn_ball hball hKclosed hK
    (hh.sub (hq.mono sdiff_subset)) hM hbound
    (fun y hy hyK => sub_eq_zero.mpr (hbd y hy hyK)) hx
  exact sub_eq_zero.mp heq



end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.BoundaryDiscontinuityCount

/-! # Finiteness of large discontinuities of monotone cluster families -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise

/-- At any positive tolerance, a monotone family of subsets of the unit disc
has only finitely many failures of one-sided Hausdorff right continuity. -/
theorem finite_large_right_continuity_failures
    (C : ℝ → Set ℂ) (ε : ℝ) (hε : 0 < ε)
    (hmono : ∀ a b, 0 < a → a ≤ b → C a ⊆ C b)
    (hbound : ∀ s, 0 < s → C s ⊆ ball (0 : ℂ) 1) :
    {t : ℝ | 0 < t ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (C s) ⊆ C t + ball (0 : ℂ) ε}.Finite := by
  let d := ε / 2
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨K, hKsub, hKfin, hcover⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).finite_cover_balls (show 0 < d / 4 by positivity)
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
  have hfinite : (⋃ y ∈ K, J y).Finite := hKfin.biUnion (fun y _ => (hJ y).finite)
  apply hfinite.subset
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

universe u

/-- Almost surely, for every centre and every positive tolerance, only
finitely many positive times fail the cluster right-continuity bound at that
tolerance. -/
theorem ae_finite_large_cluster_right_continuity_failures
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      {t : ℝ | 0 < t ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε}.Finite := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro z hz ε hε
  exact finite_large_right_continuity_failures (fun t => cluster (μ ω) 1 z t) ε hε
    (fun a b ha hab => hmono a b 1 ha hab zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball)

end HarmonicBalls


import HarmonicBalls.Proofs.Sec5.NullBoundaryContact
import HarmonicBalls.Proofs.Sec5.BoundaryJumpCount
import HarmonicBalls.Proofs.Sec5.InteriorTimeContinuity

/-! # Quantitative boundary jumps

A separated future point in a nested family of continua forces a definite
amount of new one-dimensional measure. For clusters with no new interior
points, this measure is entirely on the boundary circle.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped ENNReal MeasureTheory

/-- A point of a nested intersection at distance at least `d` from the present
set forces at least `d` one-dimensional Hausdorff measure in the increment. -/
theorem ofReal_le_hausdorffMeasure_one_iInter_sdiff
    (A : Set ℂ) (F : ℕ → Set ℂ) (z x : ℂ) (hz : z ∈ A)
    (hclosed : ∀ n, IsClosed (F n)) (hanti : Antitone F)
    (hconnected : ∀ n, IsPreconnected (F n)) (hAF : ∀ n, A ⊆ F n)
    (hx : x ∈ ⋂ n, F n) {d : ℝ}
    (hdis : Disjoint (ball x d) (closure A)) :
    ENNReal.ofReal d ≤ μH[1] ((⋂ n, F n) \ closure A) := by
  have hzd : d ≤ dist z x := by
    by_contra h
    exact Set.disjoint_left.mp hdis (mem_ball.mpr (lt_of_not_ge h)) (subset_closure hz)
  have hinterval : Ioo (0 : ℝ) d ⊆
      (fun y : ℂ => dist y x) '' ((⋂ n, F n) \ closure A) := by
    intro q hq
    have hnonempty : (sphere x q ∩ ⋂ n, F n).Nonempty := by
      by_contra h
      have hdis' : Disjoint (sphere x q) (⋂ n, F n) :=
        Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)
      obtain ⟨n, hn⟩ := (isCompact_sphere x q).elim_directed_family_closed F hclosed hdis'
        hanti.directed_ge
      have hxF : x ∈ F n := Set.mem_iInter.mp hx n
      have hzF : z ∈ F n := hAF n hz
      have hbetween : q ∈ Icc (dist x x) (dist z x) :=
        ⟨by simpa using hq.1.le, le_trans hq.2.le hzd⟩
      obtain ⟨y, hyF, hyq⟩ := (hconnected n).intermediate_value
        (f := fun y : ℂ => dist y x) hxF hzF
        (continuous_id.dist continuous_const).continuousOn hbetween
      exact Set.disjoint_left.mp hn (mem_sphere.mpr hyq) hyF
    obtain ⟨y, hyq, hyF⟩ := hnonempty
    refine ⟨y, ⟨hyF, ?_⟩, mem_sphere.mp hyq⟩
    exact fun hyA => Set.disjoint_left.mp hdis
      (mem_ball.mpr (by rw [mem_sphere.mp hyq]; exact hq.2)) hyA
  have hlip : LipschitzWith 1 (fun y : ℂ => dist y x) :=
    LipschitzWith.of_le_add (fun y z => by simpa [add_comm] using dist_triangle y z x)
  have himage := hlip.hausdorffMeasure_image_le (d := 1) (by norm_num)
    ((⋂ n, F n) \ closure A)
  have hle := (measure_mono hinterval).trans (by simpa using himage)
  rw [Real.volume_Ioo] at hle
  simpa using hle

/-- If no new interior points appear, a separated future point forces a
boundary jump whose length is at least the separation. -/
theorem ofReal_le_boundary_future_jump_of_separated_point
    {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t) {z x : ℂ} (hz : z ∈ F t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hconnected : ∀ s, 0 < s → IsPreconnected (closure (F s)))
    (hinter : (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t))
    (hx : x ∈ ⋂ n : ℕ, closure (F (t + dyadicScale n)))
    {d : ℝ} (hdis : Disjoint (ball x d) (closure (F t))) :
    ENNReal.ofReal d ≤ μH[1]
      (((⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ sphere 0 1) \ closure (F t)) := by
  let G : ℕ → Set ℂ := fun n => closure (F (t + dyadicScale n))
  have hanti : Antitone G := by
    intro i j hij
    apply closure_mono
    apply hmono _ _ (add_pos ht (dyadicScale_pos j))
    dsimp [dyadicScale]
    exact add_le_add le_rfl (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)
  have hle := ofReal_le_hausdorffMeasure_one_iInter_sdiff (F t) G z x hz
    (fun _ => isClosed_closure) hanti
    (fun n => hconnected _ (add_pos ht (dyadicScale_pos n)))
    (fun n => (hmono t _ ht (le_add_of_nonneg_right (dyadicScale_pos n).le)).trans subset_closure)
    hx hdis
  apply hle.trans (measure_mono ?_)
  intro y hy
  refine ⟨⟨hy.1, ?_⟩, hy.2⟩
  have hyclosed : y ∈ closedBall (0 : ℂ) 1 :=
    closure_minimal ((hbound _ (add_pos ht (dyadicScale_pos 0))).trans ball_subset_closedBall)
      isClosed_closedBall (Set.mem_iInter.mp hy.1 0)
  have hynot : y ∉ ball (0 : ℂ) 1 := fun hyball => hy.2 (hinter ⟨hy.1, hyball⟩)
  exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp hyclosed)
    (le_of_not_gt (by simpa only [mem_ball] using hynot)))

/-- Before a fixed horizon, separated future points of separation `d` can
occur at at most circumference divided by `d` times. -/
theorem encard_separated_future_points_le
    (F : ℝ → Set ℂ) (T d : ℝ) (hd : 0 < d)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hconnected : ∀ s, 0 < s → IsPreconnected (closure (F s)))
    (hne : ∀ s, 0 < s → (F s).Nonempty)
    (hinter : ∀ t, 0 < t →
      (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t)) :
    {t : ℝ | 0 < t ∧ t < T ∧ ∃ x ∈ ⋂ n : ℕ, closure (F (t + dyadicScale n)),
      Disjoint (ball x d) (closure (F t))}.encard ≤ ⌈2 * Real.pi / d⌉₊ := by
  apply (Set.encard_mono ?_).trans
    (encard_large_boundary_future_jumps_le (fun t => closure (F t)) T d hd
      (fun _ => isClosed_closure)
      (fun _ _ hs hst => closure_mono (hmono _ _ hs hst)))
  intro t ⟨ht, htT, x, hx, hdis⟩
  obtain ⟨z, hz⟩ := hne t ht
  exact ⟨ht, htT, ofReal_le_boundary_future_jump_of_separated_point ht hz
    hmono hbound hconnected (hinter t ht) hx hdis⟩

/-- Large failures of one-sided Hausdorff continuity are finite in number,
with an explicit bound in terms of the unit-circle circumference. -/
theorem encard_large_right_discontinuities_le
    (F : ℝ → Set ℂ) (T d : ℝ) (hd : 0 < d)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hconnected : ∀ s, 0 < s → IsPreconnected (closure (F s)))
    (hne : ∀ s, 0 < s → (F s).Nonempty)
    (hinter : ∀ t, 0 < t →
      (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t)) :
    {t : ℝ | 0 < t ∧ t < T ∧ ¬ ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (F s) ⊆ thickening d (closure (F t))}.encard ≤
      ⌈2 * Real.pi / d⌉₊ := by
  apply (Set.encard_mono ?_).trans
    (encard_separated_future_points_le F T d hd hmono hbound hconnected hne hinter)
  intro t ⟨ht, htT, hfail⟩
  have hnot : ¬ (⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))) ⊆
      thickening d (closure (F t)) := by
    intro hsub
    exact hfail (eventually_closure_subset_open_of_iInter_subset ht hmono hbound
      isOpen_thickening hsub)
  obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot
  refine ⟨ht, htT, x, by simpa only [dyadicScale] using hx, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hyF
  apply hxnot
  apply mem_thickening_iff.mpr
  exact ⟨y, hyF, by simpa only [mem_ball, dist_comm] using hy⟩

universe u

/-- Almost surely, simultaneously for all centres, the number of times
before `T` with a future point at separation `d` has the circumference bound. -/
theorem ae_encard_separated_cluster_future_points_le
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ T d : ℝ, 0 < d →
      {t : ℝ | 0 < t ∧ t < T ∧
        ∃ x ∈ ⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n)),
          Disjoint (ball x d) (closure (cluster (μ ω) 1 z t))}.encard ≤
        ⌈2 * Real.pi / d⌉₊ := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hinter
  intro z hz T d hd
  apply encard_separated_future_points_le (fun t => cluster (μ ω) 1 z t) T d hd
  · exact fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz
  · exact fun _ _ => cluster_subset_ball
  · exact fun s hs => (hopen s 1 hs zero_lt_one z hz).2.1.isPreconnected.closure
  · exact fun _ _ => ⟨z, self_mem_cluster hz⟩
  · exact fun t ht => hinter t ht z hz

/-- Almost surely, large one-sided Hausdorff discontinuities have the same
explicit finite bound, simultaneously for all poles and positive separations. -/
theorem ae_encard_large_cluster_right_discontinuities_le
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ T d : ℝ, 0 < d →
      {t : ℝ | 0 < t ∧ t < T ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ thickening d (closure (cluster (μ ω) 1 z t))}.encard ≤
        ⌈2 * Real.pi / d⌉₊ := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hinter
  intro z hz T d hd
  apply encard_large_right_discontinuities_le (fun t => cluster (μ ω) 1 z t) T d hd
  · exact fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz
  · exact fun _ _ => cluster_subset_ball
  · exact fun s hs => (hopen s 1 hs zero_lt_one z hz).2.1.isPreconnected.closure
  · exact fun _ _ => ⟨z, self_mem_cluster hz⟩
  · exact fun t ht => hinter t ht z hz

end HarmonicBalls

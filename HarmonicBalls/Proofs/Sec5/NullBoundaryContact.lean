import HarmonicBalls.Proofs.Sec5.CountableBoundaryContact
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Boundary contact with null one-dimensional Hausdorff measure -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal MeasureTheory

/-- A nested intersection of closed preconnected sets containing a common point
of `A` has no points outside `closure A` when that difference has zero
one-dimensional Hausdorff measure. -/
theorem iInter_subset_closure_of_hausdorffMeasure_one_sdiff_zero
    (A : Set ℂ) (F : ℕ → Set ℂ) (z : ℂ) (hz : z ∈ A)
    (hclosed : ∀ n, IsClosed (F n)) (hanti : Antitone F)
    (hconnected : ∀ n, IsPreconnected (F n)) (hAF : ∀ n, A ⊆ F n)
    (hnull : μH[1] ((⋂ n, F n) \ closure A) = 0) :
    (⋂ n, F n) ⊆ closure A := by
  intro x hx
  by_contra hxA
  obtain ⟨d, hd, hdsub⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hxA
  have hzd : d ≤ dist z x := by
    by_contra h
    exact (hdsub (mem_ball.mpr (lt_of_not_ge h))) (subset_closure hz)
  have hinterval : Ioo (0 : ℝ) d ⊆ (fun y : ℂ => dist y x) '' ((⋂ n, F n) \ closure A) := by
    intro q hq
    have hnonempty : (sphere x q ∩ ⋂ n, F n).Nonempty := by
      by_contra h
      have hdis : Disjoint (sphere x q) (⋂ n, F n) := Set.disjoint_iff_inter_eq_empty.mpr
        (Set.not_nonempty_iff_eq_empty.mp h)
      obtain ⟨n, hn⟩ := (isCompact_sphere x q).elim_directed_family_closed F hclosed hdis
        hanti.directed_ge
      have hxF : x ∈ F n := Set.mem_iInter.mp hx n
      have hzF : z ∈ F n := hAF n hz
      have hbetween : q ∈ Icc (dist x x) (dist z x) :=
        ⟨by simpa using hq.1.le, le_trans hq.2.le hzd⟩
      obtain ⟨y, hyF, hyq⟩ := (hconnected n).intermediate_value (f := fun y : ℂ => dist y x)
        hxF hzF (continuous_id.dist continuous_const).continuousOn hbetween
      exact Set.disjoint_left.mp hn (mem_sphere.mpr hyq) hyF
    obtain ⟨y, hyq, hyF⟩ := hnonempty
    refine ⟨y, ⟨hyF, ?_⟩, mem_sphere.mp hyq⟩
    exact hdsub (mem_ball.mpr (by rw [mem_sphere.mp hyq]; exact hq.2))
  have hlip : LipschitzWith 1 (fun y : ℂ => dist y x) :=
    LipschitzWith.of_le_add (fun y z => by simpa [add_comm] using dist_triangle y z x)
  have himage : μH[1] ((fun y : ℂ => dist y x) '' ((⋂ n, F n) \ closure A)) = 0 := by
    apply le_antisymm _ bot_le
    have h := hlip.hausdorffMeasure_image_le (d := 1) (by norm_num)
      ((⋂ n, F n) \ closure A)
    simpa [hnull] using h
  have hzero : volume (Ioo (0 : ℝ) d) = 0 := by
    rw [← MeasureTheory.hausdorffMeasure_real]
    exact measure_mono_null hinterval himage
  rw [Real.volume_Ioo] at hzero
  exact (ENNReal.ofReal_pos.mpr hd).ne' (by simpa using hzero)

universe u

/-- If increment masses vanish, a set of new boundary points of zero one-dimensional Hausdorff measure cannot
cause a right discontinuity. The nullity premise is geometric and is not
asserted here for Liouville clusters. -/
theorem ae_cluster_right_continuity_of_vanishing_increment_and_null_boundary
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
          ENNReal.ofReal ε) →
      (μH[1] (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ sphere 0 1) \
        closure (cluster (μ ω) 1 z t)) = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_of_vanishing_increment
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_cluster_right_continuity_of_vanishing_increment_and_sphere_inclusion
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hconnected hmono hinterior hcontinuity
  intro t ht z hz hsmall hnull
  let F : ℕ → Set ℂ := fun n => closure (cluster (μ ω) 1 z (t + dyadicScale n))
  have hnew : μH[1] ((⋂ n, F n) \ closure (cluster (μ ω) 1 z t)) = 0 := by
    apply measure_mono_null _ hnull
    intro x hx
    refine ⟨⟨hx.1, ?_⟩, hx.2⟩
    have hxclosed : x ∈ closedBall (0 : ℂ) 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
        (Set.mem_iInter.mp hx.1 0)
    have hxnotball : x ∉ ball (0 : ℂ) 1 := by
      intro hxb
      exact hx.2 (hinterior t ht z hz hsmall ⟨hx.1, hxb⟩)
    apply mem_sphere.mpr
    exact le_antisymm (mem_closedBall.mp hxclosed)
      (le_of_not_gt (by simpa only [mem_ball] using hxnotball))
  have hsub : (⋂ n, F n) ⊆ closure (cluster (μ ω) 1 z t) := by
    apply iInter_subset_closure_of_hausdorffMeasure_one_sdiff_zero _ F z (self_mem_cluster hz)
    · exact fun _ => isClosed_closure
    · intro i j hij
      apply closure_mono
      have hscale : dyadicScale j ≤ dyadicScale i := by
        dsimp [dyadicScale]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
      exact hmono _ _ 1 (add_pos ht (dyadicScale_pos j)) (by linarith)
        zero_lt_one z hz
    · intro n
      exact (hconnected (t + dyadicScale n) 1 (add_pos ht (dyadicScale_pos n))
        zero_lt_one z hz).2.1.isPreconnected.closure
    · intro n x hx
      exact subset_closure (hmono t (t + dyadicScale n) 1 ht
        (le_add_of_nonneg_right (dyadicScale_pos n).le) zero_lt_one z hz hx)
    · exact hnew
  apply hcontinuity t ht z hz hsmall
  intro x hx
  exact hsub hx.1

end HarmonicBalls


import HarmonicBalls.Proofs.Sec5.NullBoundaryContact
import HarmonicBalls.Proofs.Sec5.BoundaryJumpCount

/-! # Geometric size of boundary jumps -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped BigOperators ENNReal MeasureTheory

/-- If a nested intersection of closed preconnected sets acquires a point at
least `d` away from a closed set containing a common point, its new part has
one-dimensional Hausdorff measure at least `d`. -/
theorem ofReal_le_hausdorffMeasure_one_sdiff_of_separated_point
    (A : Set ℂ) (F : ℕ → Set ℂ) (z x : ℂ) (d : ℝ)
    (hz : z ∈ A) (hx : x ∈ ⋂ n, F n)
    (hsep : ball x d ⊆ (closure A)ᶜ)
    (hclosed : ∀ n, IsClosed (F n)) (hanti : Antitone F)
    (hconnected : ∀ n, IsPreconnected (F n)) (hAF : ∀ n, A ⊆ F n) :
    ENNReal.ofReal d ≤ μH[1] ((⋂ n, F n) \ closure A) := by
  have hzd : d ≤ dist z x := by
    by_contra h
    exact (hsep (mem_ball.mpr (lt_of_not_ge h))) (subset_closure hz)
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
    exact hsep (mem_ball.mpr (by rw [mem_sphere.mp hyq]; exact hq.2))
  have hlip : LipschitzWith 1 (fun y : ℂ => dist y x) :=
    LipschitzWith.of_le_add (fun y z => by simpa [add_comm] using dist_triangle y z x)
  have hmeasure := hlip.hausdorffMeasure_image_le (d := 1) (by norm_num)
    ((⋂ n, F n) \ closure A)
  have hintervalmeasure : μH[1] (Ioo (0 : ℝ) d) ≤
      μH[1] ((fun y : ℂ => dist y x) '' ((⋂ n, F n) \ closure A)) := measure_mono hinterval
  rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Ioo] at hintervalmeasure
  rw [MeasureTheory.hausdorffMeasure_real] at hmeasure
  simpa using hintervalmeasure.trans hmeasure

/-- Separated new boundary points, with no new interior points, consume at
least their separation in one-dimensional boundary measure. -/
theorem ofReal_le_boundary_jump_of_separated_point
    (A : Set ℂ) (F : ℕ → Set ℂ) (z x : ℂ) (d : ℝ)
    (hz : z ∈ A) (hx : x ∈ ⋂ n, F n)
    (hsep : ball x d ⊆ (closure A)ᶜ)
    (hclosed : ∀ n, IsClosed (F n)) (hanti : Antitone F)
    (hconnected : ∀ n, IsPreconnected (F n)) (hAF : ∀ n, A ⊆ F n)
    (hboundary : ((⋂ n, F n) \ closure A) ⊆ sphere (0 : ℂ) 1) :
    ENNReal.ofReal d ≤ μH[1] (((⋂ n, F n) ∩ sphere (0 : ℂ) 1) \ closure A) := by
  exact (ofReal_le_hausdorffMeasure_one_sdiff_of_separated_point A F z x d hz hx hsep
    hclosed hanti hconnected hAF).trans (measure_mono (fun y hy => ⟨⟨hy.1, hboundary hy⟩, hy.2⟩))

/-- For an increasing family of connected sets with a common point, there
are at most `⌈2π / d⌉` times before `T` at which a new boundary point is
separated by `d`, provided that all new points at that time lie on the
unit circle. -/
theorem encard_separated_boundary_jumps_le
    (C : ℝ → Set ℂ) (z : ℂ) (T d : ℝ) (hd : 0 < d)
    (hz : ∀ t, 0 < t → z ∈ C t)
    (hconnected : ∀ t, 0 < t → IsPreconnected (closure (C t)))
    (hmono : ∀ a b, 0 < a → a ≤ b → C a ⊆ C b) :
    {t : ℝ | 0 < t ∧ t < T ∧
      ((⋂ n : ℕ, closure (C (t + dyadicScale n))) \ closure (C t)) ⊆ sphere (0 : ℂ) 1 ∧
      ∃ x ∈ ⋂ n : ℕ, closure (C (t + dyadicScale n)),
        ball x d ⊆ (closure (C t))ᶜ}.encard ≤ ⌈2 * Real.pi / d⌉₊ := by
  apply (Set.encard_mono (show {t : ℝ | 0 < t ∧ t < T ∧
      ((⋂ n : ℕ, closure (C (t + dyadicScale n))) \ closure (C t)) ⊆ sphere (0 : ℂ) 1 ∧
      ∃ x ∈ ⋂ n : ℕ, closure (C (t + dyadicScale n)),
        ball x d ⊆ (closure (C t))ᶜ} ⊆
      {t : ℝ | 0 < t ∧ t < T ∧ ENNReal.ofReal d ≤
        μH[1] (((⋂ n : ℕ, closure (C (t + dyadicScale n))) ∩ sphere (0 : ℂ) 1) \ closure (C t))} from ?_)).trans
    (encard_large_boundary_future_jumps_le (fun t => closure (C t)) T d hd
      (fun _ => isClosed_closure)
      (fun a b ha hab => closure_mono (hmono a b ha hab)))
  intro t ht
  obtain ⟨htpos, htT, hboundary, x, hx, hsep⟩ := ht
  refine ⟨htpos, htT, ?_⟩
  apply ofReal_le_boundary_jump_of_separated_point (C t)
    (fun n => closure (C (t + dyadicScale n))) z x d (hz t htpos) hx hsep
  · exact fun _ => isClosed_closure
  · intro i j hij
    apply closure_mono
    apply hmono _ _ (add_pos htpos (dyadicScale_pos j))
    have hscale : dyadicScale j ≤ dyadicScale i := by
      dsimp [dyadicScale]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
    linarith
  · intro n
    exact hconnected _ (add_pos htpos (dyadicScale_pos n))
  · intro n
    exact (hmono _ _ htpos (le_add_of_nonneg_right (dyadicScale_pos n).le)).trans subset_closure
  · exact hboundary

universe u

/-- For Liouville clusters, the number of separated boundary jumps with
vanishing increment mass is bounded by the circumference divided by the
separation. -/
theorem ae_encard_separated_boundary_jumps_le
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ∀ d : ℝ, 0 < d →
      {t : ℝ | 0 < t ∧ t < T ∧
        (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
          μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
            ENNReal.ofReal ε) ∧
        ∃ x ∈ ⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n)),
          ball x d ⊆ (closure (cluster (μ ω) 1 z t))ᶜ}.encard ≤ ⌈2 * Real.pi / d⌉₊ := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_of_vanishing_increment
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hconnected hmono hinterior
  intro T z hz d hd
  apply (Set.encard_mono (show {t : ℝ | 0 < t ∧ t < T ∧
      (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
          ENNReal.ofReal ε) ∧
      ∃ x ∈ ⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n)),
        ball x d ⊆ (closure (cluster (μ ω) 1 z t))ᶜ} ⊆
      {t : ℝ | 0 < t ∧ t < T ∧
        ((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) \
          closure (cluster (μ ω) 1 z t)) ⊆ sphere (0 : ℂ) 1 ∧
      ∃ x ∈ ⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n)),
        ball x d ⊆ (closure (cluster (μ ω) 1 z t))ᶜ} from ?_)).trans
    (encard_separated_boundary_jumps_le (fun t => cluster (μ ω) 1 z t) z T d hd
      (fun _ _ => self_mem_cluster hz)
      (fun t ht => (hconnected t 1 ht zero_lt_one z hz).2.1.isPreconnected.closure)
      (fun a b ha hab => hmono a b 1 ha hab zero_lt_one z hz))
  intro t ht
  obtain ⟨htpos, htT, hsmall, hx⟩ := ht
  refine ⟨htpos, htT, ?_, hx⟩
  intro x hx'
  have hxclosed : x ∈ closedBall (0 : ℂ) 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
      (Set.mem_iInter.mp hx'.1 0)
  have hxnotball : x ∉ ball (0 : ℂ) 1 := by
    intro hxb
    exact hx'.2 (hinterior t htpos z hz hsmall ⟨hx'.1, hxb⟩)
  apply mem_sphere.mpr
  exact le_antisymm (mem_closedBall.mp hxclosed)
    (le_of_not_gt (by simpa only [mem_ball] using hxnotball))

end HarmonicBalls


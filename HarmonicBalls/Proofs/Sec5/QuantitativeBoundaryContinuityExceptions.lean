import HarmonicBalls.Proofs.Sec5.BoundaryJumpAttachment
import HarmonicBalls.Proofs.Sec5.BoundaryJumpCount
import HarmonicBalls.Proofs.Sec5.BoundaryContinuityCompactness

/-! # Quantitative control of possible continuity exceptions

A possible jump which prevents containment at scale `ε` must consume at
least `ε` of the unit circle's one-dimensional Hausdorff measure. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal MeasureTheory

/-- Failure of one-sided containment at scale `ε` produces a new point at
least `ε` from every point of the present closed set. -/
theorem exists_future_point_separated_of_not_eventually_subset
    {F : ℝ → Set ℂ} {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hfail : ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (F s) ⊆ F t + ball (0 : ℂ) ε) :
    ∃ x ∈ rightClosedEnvelope F t \ closure (F t),
      ∀ y ∈ closure (F t), ε ≤ dist x y := by
  have hnot : ¬ rightClosedEnvelope F t ⊆ thickening ε (F t) := by
    intro hsub
    apply hfail
    obtain ⟨δ, hδ, hδ'⟩ := eventually_closure_subset_open_of_iInter_subset ht hmono hbound
      (U := thickening ε (F t)) isOpen_thickening (by simpa [rightClosedEnvelope] using hsub)
    refine ⟨δ, hδ, fun s hs x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp (hδ' s hs hx)
    refine ⟨y, hy, x - y, ?_, by abel⟩
    simpa [mem_ball, dist_eq_norm] using hxy
  obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot
  have hsep : ∀ y ∈ closure (F t), ε ≤ dist x y := by
    intro y hy
    apply le_of_not_gt
    intro hxy
    apply hxnot
    rw [← thickening_closure]
    exact mem_thickening_iff.mpr ⟨y, hy, hxy⟩
  exact ⟨x, ⟨hx, fun hxold => (not_lt_of_ge (hsep x hxold)) (by simpa using hε)⟩, hsep⟩

/-- For a monotone bounded family whose jump components attach to the old
set, at most `⌈2π / ε⌉` positive times before `T` can fail one-sided
containment at scale `ε`. -/
theorem encard_not_eventually_subset_le
    (F : ℝ → Set ℂ) (T ε : ℝ) (hε : 0 < ε)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hattach : ∀ t, 0 < t → ∀ x ∈ rightClosedEnvelope F t \ closure (F t),
      (closure (connectedComponentIn (rightClosedEnvelope F t \ closure (F t)) x) ∩
        closure (F t)).Nonempty)
    (hcircle : ∀ t, 0 < t → rightClosedEnvelope F t \ closure (F t) ⊆ sphere (0 : ℂ) 1) :
    {t : ℝ | 0 < t ∧ t < T ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (F s) ⊆ F t + ball (0 : ℂ) ε}.encard ≤ ⌈2 * Real.pi / ε⌉₊ := by
  apply le_trans (Set.encard_mono ?_) (encard_large_boundary_future_jumps_le
    (fun s => closure (F s)) T ε hε (fun _ => isClosed_closure)
    (fun a b ha hab => closure_mono (hmono a b ha hab)))
  intro t ht
  obtain ⟨x, hx, hsep⟩ := exists_future_point_separated_of_not_eventually_subset
    ht.1 hε hmono hbound ht.2.2
  obtain ⟨y, hycomp, hyold⟩ := hattach t ht.1 x hx
  have hlength : ENNReal.ofReal ε ≤ μH[1] (connectedComponentIn
      (rightClosedEnvelope F t \ closure (F t)) x) :=
    (ENNReal.ofReal_le_ofReal (hsep y hyold)).trans
      (ofReal_dist_le_hausdorffMeasure_one_of_closure isPreconnected_connectedComponentIn
        (mem_connectedComponentIn hx) hycomp)
  refine ⟨ht.1, ht.2.1, hlength.trans (measure_mono ?_)⟩
  intro w hw
  have hw' := connectedComponentIn_subset (rightClosedEnvelope F t \ closure (F t)) x hw
  exact ⟨⟨by simpa only [rightClosedEnvelope, dyadicScale] using hw'.1,
    hcircle t ht.1 hw'⟩, hw'.2⟩

universe u

/-- Almost surely, simultaneously for every centre, horizon and positive
`ε`, there are at most `⌈2π / ε⌉` times at which one-sided cluster
containment fails at scale `ε`. -/
theorem ae_encard_cluster_containment_exceptions_le
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      {t : ℝ | 0 < t ∧ t < T ∧ ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε}.encard ≤
        ⌈2 * Real.pi / ε⌉₊ := by
  filter_upwards [h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_boundary_jump_component_attaches hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hmono hattach hinter
  intro T z hz ε hε
  apply encard_not_eventually_subset_le (fun s => cluster (μ ω) 1 z s) T ε hε
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball)
  · intro t ht x hx
    obtain ⟨y, hy, hyold, _⟩ := hattach t ht z hz x hx
    exact ⟨y, hy, hyold⟩
  · intro t ht x hx
    have hclosed : x ∈ closedBall (0 : ℂ) 1 :=
      (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall)
        (mem_iInter.mp hx.1 0)
    have hnot : x ∉ ball (0 : ℂ) 1 := fun hxb => hx.2 (by
      apply hinter t ht z hz
      exact ⟨by simpa only [rightClosedEnvelope, dyadicScale] using hx.1, hxb⟩)
    apply mem_sphere.mpr
    exact le_antisymm (mem_closedBall.mp hclosed)
      (le_of_not_gt (by simpa only [mem_ball] using hnot))

#print axioms exists_future_point_separated_of_not_eventually_subset
#print axioms encard_not_eventually_subset_le
#print axioms ae_encard_cluster_containment_exceptions_le

end HarmonicBalls

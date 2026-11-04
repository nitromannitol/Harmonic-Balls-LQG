import HarmonicBalls.Proofs.Sec5.LocalContactFamily
import HarmonicBalls.Steps.Sec5.CompactContinuity
import HarmonicBalls.Proofs.Sec5.ContactDiscComparison

/-! # Field-local first boundary contact times -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology Pointwise

universe u

/-- The centre-specific field-local horizons are the actual first boundary
contact times: compact containment holds exactly before the horizon, and the
cluster touches the circle at that time. Mass conservation and Hausdorff
continuity hold through the horizon. The proposed locality, affine-invariance
and coordinate-change hypotheses are explicit and await source review. -/
theorem exists_fieldLocal_firstContact_horizons
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ H : Ω → (ball (0 : ℂ) 1 → ℝ≥0∞),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H ∧
      ∀ᵐ ω ∂P, ∀ z : ball (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) (1 / 2) →
        0 < H ω z ∧ H ω z ≤ μ ω (ball 0 1) ∧ H ω z < ⊤ ∧
        (∀ t : ℝ, 0 < t →
          (closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ↔ t < (H ω z).toReal)) ∧
        (closure (cluster (μ ω) 1 z (H ω z).toReal) ∩ sphere (0 : ℂ) 1).Nonempty ∧
        cluster (μ ω) 1 z (H ω z).toReal = cluster (μ ω) 2 z (H ω z).toReal ∧
        ∀ t ∈ Ioc (0 : ℝ) (H ω z).toReal,
          μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t ∧
          ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
            hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε := by
  obtain ⟨H, hH, hHω⟩ := exists_fieldLocal_centre_horizons_with_continuity
    hI2 h53 h54 h71 h72 hAff hCC hγ hγ2 hα hGFF hμ hloc
  have hmono := clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hcompact := clusterCompactRightContinuity_of_steps (clusterMonotone_proved hI2) h72
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  refine ⟨H, hH, ?_⟩
  have hcompare := ae_cluster_eq_larger_disc_at_first_contact hI2 hγ hγ2 hα hGFF hμ
    (R := 2) (by norm_num)
  filter_upwards [hHω, hmono, hcompact, hcompare] with ω hHω hmono hcompact hcompare
  intro z hz
  obtain ⟨hpos, hbound, hfin, hchar, hcont⟩ := hHω z hz
  have hT : 0 < (H ω z).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hbefore : ∀ t ∈ Ioo (0 : ℝ) (H ω z).toReal,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
    intro t ht
    have htH : ENNReal.ofReal t < H ω z := by
      calc
        _ < ENNReal.ofReal (H ω z).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2
        _ = H ω z := ENNReal.ofReal_toReal hfin.ne
    obtain ⟨s, hts, hs⟩ := (hchar t ht.1).mp htH
    exact (closure_mono (hmono t s 1 ht.1 hts.le zero_lt_one z z.property)).trans hs
  have hnot : ¬ closure (cluster (μ ω) 1 z (H ω z).toReal) ⊆ ball 0 1 := by
    intro hin
    have hK : IsCompact (closure (cluster (μ ω) 1 z (H ω z).toReal)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_ball.subset hin)
    obtain ⟨ε, hε, hεsub⟩ := hK.exists_thickening_subset_open isOpen_ball hin
    obtain ⟨δ, hδ, hδbound⟩ := hcompact z hz (H ω z).toReal hT hin ε hε
    have hlater : closure (cluster (μ ω) 1 z ((H ω z).toReal + δ / 2)) ⊆ ball 0 1 := by
      intro x hx
      apply hεsub
      have hxsum := hδbound ((H ω z).toReal + δ / 2) ⟨by linarith, by linarith⟩ hx
      obtain ⟨y, hy, w, hw, rfl⟩ := hxsum
      apply mem_thickening_iff.2
      refine ⟨y, subset_closure hy, ?_⟩
      simp only [mem_ball, dist_zero_right] at hw
      simpa only [dist_eq_norm, add_sub_cancel_left] using hw
    have hlt : ENNReal.ofReal (H ω z).toReal < H ω z :=
      (hchar (H ω z).toReal hT).mpr ⟨_, by linarith, hlater⟩
    rw [ENNReal.ofReal_toReal hfin.ne] at hlt
    exact (lt_irrefl _ hlt)
  have hcontact : (closure (cluster (μ ω) 1 z (H ω z).toReal) ∩ sphere (0 : ℂ) 1).Nonempty := by
    obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot
    have hxclosed : x ∈ closedBall (0 : ℂ) 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall hx
    have hxsphere : x ∈ sphere (0 : ℂ) 1 := by
      simp only [mem_closedBall] at hxclosed
      simp only [mem_ball, not_lt] at hxnot
      exact le_antisymm hxclosed hxnot
    exact ⟨x, hx, hxsphere⟩
  refine ⟨hpos, hbound, hfin, ?_, hcontact, hcompare z z.property _ hT hbefore, hcont⟩
  intro t ht
  constructor
  · intro hin
    by_contra h
    have hle : (H ω z).toReal ≤ t := le_of_not_gt h
    exact hnot ((closure_mono (hmono (H ω z).toReal t 1 hT hle zero_lt_one z z.property)).trans hin)
  · intro hlt
    exact hbefore t ⟨ht, hlt⟩

end HarmonicBalls

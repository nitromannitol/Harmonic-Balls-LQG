import HarmonicBalls.Proofs.Sec5.LocalContactFamily
import HarmonicBalls.Proofs.Sec5.ContactDiscComparison
import HarmonicBalls.Proofs.Sec5.ExitTime

/-! # First contact from compact continuity -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology Pointwise

universe u

/-- The first-contact family is field-local and finite using compact cluster
continuity, without assuming the regularized harmonic-ball theorem or any
field scaling law. The proposed field-locality input awaits source review. -/
theorem exists_fieldLocal_firstContact_of_compact_continuity
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
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
          μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_centre_containment_horizons
    hI2 hγ hγ2 hα hGFF hμ hloc (R := 1) zero_lt_one
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
  have hmass := clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hmono := clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hboundary := h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hcompact := clusterCompactRightContinuity_of_steps (clusterMonotone_proved hI2) h72
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hcompare := ae_cluster_eq_larger_disc_at_first_contact hI2 hγ hγ2 hα hGFF hμ
    (R := 2) (by norm_num)
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, hsmall.ae_eventually_dyadic, hμ, hmass, hmono, hboundary, hcompact, hcompare]
    with ω hchar hsmall hμω hmass hmono hboundary hcompact hcompare
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  intro z hz
  have hsmallz : ∃ s : ℝ, 0 < s ∧ closure (cluster (μ ω) 1 z s) ⊆ ball 0 1 := by
    obtain ⟨m, hm⟩ := hsmall.exists
    refine ⟨(2 : ℝ)⁻¹ ^ m, by positivity, ?_⟩
    intro x hx
    have h := hm ((2 : ℝ)⁻¹ ^ m) ⟨by positivity, le_rfl⟩ z hz hx
    simp only [mem_ball] at h hz ⊢
    have htri := dist_triangle x z (0 : ℂ)
    norm_num at h
    linarith
  obtain ⟨s, hs, hsinside⟩ := hsmallz
  have hpos : 0 < H ω z := by
    have hlt : ENNReal.ofReal (s / 2) < H ω z :=
      (hchar z (s / 2) (by linarith)).mpr ⟨s, by linarith, hsinside⟩
    exact lt_trans (ENNReal.ofReal_pos.mpr (by linarith)) hlt
  have hμfin : μ ω (ball (0 : ℂ) 1) < ⊤ := measure_ball_lt_top
  have hbound : H ω z ≤ μ ω (ball (0 : ℂ) 1) := by
    by_contra hn
    obtain ⟨q, hqlo, hqhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hqpos : 0 < (q : ℝ) := by
      have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqlo
      exact_mod_cast hqpos'
    have hqhi' : ENNReal.ofReal (q : ℝ) < H ω z := by simpa using hqhi
    obtain ⟨v, hqv, hv⟩ := (hchar z q hqpos).mp hqhi'
    have hcl : closure (cluster (μ ω) 1 z q) ⊆ ball 0 1 :=
      (closure_mono (hmono q v 1 hqpos hqv.le zero_lt_one z z.property)).trans hv
    have heq := (hmass 1 q zero_lt_one hqpos z z.property).2.2 hcl
      (hboundary z z.property q hqpos hcl)
    have hle : ENNReal.ofReal (q : ℝ) ≤ μ ω (ball (0 : ℂ) 1) := by
      rw [← heq]
      exact measure_mono cluster_subset_ball
    have hlo : μ ω (ball (0 : ℂ) 1) < ENNReal.ofReal (q : ℝ) := by simpa using hqlo
    exact (not_lt_of_ge hle) hlo
  have hfin : H ω z < ⊤ := lt_of_le_of_lt hbound hμfin
  have hT : 0 < (H ω z).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hbefore : ∀ t ∈ Ioo (0 : ℝ) (H ω z).toReal,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
    intro t ht
    have htH : ENNReal.ofReal t < H ω z := by
      calc
        _ < ENNReal.ofReal (H ω z).toReal := (ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2
        _ = H ω z := ENNReal.ofReal_toReal hfin.ne
    obtain ⟨v, htv, hv⟩ := (hchar z t ht.1).mp htH
    exact (closure_mono (hmono t v 1 ht.1 htv.le zero_lt_one z z.property)).trans hv
  have hnot : ¬ closure (cluster (μ ω) 1 z (H ω z).toReal) ⊆ ball 0 1 := by
    intro hin
    have hK : IsCompact (closure (cluster (μ ω) 1 z (H ω z).toReal)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_ball.subset hin)
    obtain ⟨ε, hε, hεsub⟩ := hK.exists_thickening_subset_open isOpen_ball hin
    obtain ⟨δ, hδ, hδbound⟩ := hcompact z hz (H ω z).toReal hT hin ε hε
    have hlater : closure (cluster (μ ω) 1 z ((H ω z).toReal + δ / 2)) ⊆ ball 0 1 := by
      intro x hx
      apply hεsub
      obtain ⟨y, hy, w, hw, rfl⟩ := hδbound _ ⟨by linarith, by linarith⟩ hx
      apply mem_thickening_iff.2
      refine ⟨y, subset_closure hy, ?_⟩
      simp only [mem_ball, dist_zero_right] at hw
      simpa only [dist_eq_norm, add_sub_cancel_left] using hw
    have hlt : ENNReal.ofReal (H ω z).toReal < H ω z :=
      (hchar z (H ω z).toReal hT).mpr ⟨_, by linarith, hlater⟩
    rw [ENNReal.ofReal_toReal hfin.ne] at hlt
    exact lt_irrefl _ hlt
  have hcontact : (closure (cluster (μ ω) 1 z (H ω z).toReal) ∩ sphere (0 : ℂ) 1).Nonempty := by
    obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot
    have hxclosed : x ∈ closedBall (0 : ℂ) 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall hx
    have hxsphere : x ∈ sphere (0 : ℂ) 1 := by
      simp only [mem_closedBall] at hxclosed
      simp only [mem_ball, not_lt] at hxnot
      exact le_antisymm hxclosed hxnot
    exact ⟨x, hx, hxsphere⟩
  have hmass_before : ∀ t ∈ Ioo (0 : ℝ) (H ω z).toReal,
      μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t := by
    intro t ht
    have htcl := hbefore t ht
    exact (hmass 1 t zero_lt_one ht.1 z z.property).2.2 htcl
      (hboundary z z.property t ht.1 htcl)
  refine ⟨hpos, hbound, hfin, ?_, hcontact, hcompare z z.property _ hT hbefore, ?_⟩
  · intro t ht
    constructor
    · intro hin
      by_contra h
      have hle : (H ω z).toReal ≤ t := le_of_not_gt h
      exact hnot ((closure_mono (hmono (H ω z).toReal t 1 hT hle zero_lt_one z z.property)).trans hin)
    · intro hlt
      exact hbefore t ⟨ht, hlt⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact hmass_before t ⟨ht.1, hlt⟩
    · apply cluster_measure_eq_of_earlier_mass_eq (μ ω) 1 z hT
      · intro v hv
        exact hmono v (H ω z).toReal 1 hv.1 hv.2.le zero_lt_one z z.property
      · exact (hmass 1 (H ω z).toReal zero_lt_one hT z z.property).1
      · exact hmass_before

end HarmonicBalls

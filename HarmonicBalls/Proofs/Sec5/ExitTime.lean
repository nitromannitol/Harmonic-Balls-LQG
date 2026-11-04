import HarmonicBalls.Proofs.Sec5.LeftContinuity

/-! # Exit times of increasing clusters -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise Topology

/-- The supremum of compact-containment times is a positive exit time. A
right-hand persistence estimate rules out compact containment at the
supremum, and openness identifies the closures before and after regularizing. -/
theorem exists_exit_time_of_monotone
    {C : ℝ → Set ℂ}
    (hopen : ∀ t : ℝ, 0 < t → IsOpen (C t))
    (hmono : MonotoneOn C (Ioi 0))
    (hball : ∀ t : ℝ, 0 < t → C t ⊆ ball (0 : ℂ) 1)
    (hsmall : ∃ t : ℝ, 0 < t ∧ closure (C t) ⊆ ball 0 1)
    (hlarge : ∃ t : ℝ, 0 < t ∧ ¬ closure (C t) ⊆ ball 0 1)
    (hpersist : ∀ t : ℝ, 0 < t → closure (C t) ⊆ ball 0 1 →
      ∃ t' : ℝ, t < t' ∧ closure (C t') ⊆ ball 0 1) :
    ∃ T : ℝ, 0 < T ∧ (∀ t ∈ Ioo 0 T, closure (C t) ⊆ ball 0 1) ∧
      (closure (interior (closure (C T))) ∩ sphere (0 : ℂ) 1).Nonempty := by
  let S : Set ℝ := {t | 0 < t ∧ closure (C t) ⊆ ball 0 1}
  obtain ⟨a, ha, haS⟩ := hsmall
  have hne : S.Nonempty := ⟨a, ha, haS⟩
  obtain ⟨b, hb, hbnot⟩ := hlarge
  have hbdd : BddAbove S := by
    refine ⟨b, ?_⟩
    intro s hs
    by_contra hsb
    have hbs : b ≤ s := (not_le.1 hsb).le
    exact hbnot ((closure_mono (hmono hb hs.1 hbs)).trans hs.2)
  let T := sSup S
  have hT : 0 < T := lt_of_lt_of_le ha (le_csSup hbdd ⟨ha, haS⟩)
  have hbefore : ∀ t ∈ Ioo (0 : ℝ) T, closure (C t) ⊆ ball 0 1 := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne ht.2
    exact (closure_mono (hmono ht.1 hs.1 hts.le)).trans hs.2
  have hnot : ¬ closure (C T) ⊆ ball 0 1 := by
    intro hinside
    obtain ⟨t, hTt, htinside⟩ := hpersist T hT hinside
    have htS : t ∈ S := ⟨lt_trans hT hTt, htinside⟩
    exact (not_lt_of_ge (le_csSup hbdd htS)) hTt
  obtain ⟨x, hxcl, hxnot⟩ := Set.not_subset.1 hnot
  have hxclosed : x ∈ closedBall (0 : ℂ) 1 :=
    closure_minimal ((hball T hT).trans ball_subset_closedBall) isClosed_closedBall hxcl
  have hxsphere : x ∈ sphere (0 : ℂ) 1 := by
    simp only [mem_closedBall] at hxclosed
    simp only [mem_ball, not_lt] at hxnot
    exact le_antisymm hxclosed hxnot
  have hclosure : closure (interior (closure (C T))) = closure (C T) := by
    apply Subset.antisymm
    · simpa using closure_mono (interior_subset : interior (closure (C T)) ⊆ closure (C T))
    · exact closure_mono ((hopen T hT).subset_interior_iff.2 subset_closure)
  exact ⟨T, hT, hbefore, ⟨x, hclosure.symm ▸ hxcl, hxsphere⟩⟩

universe u

/-- The exit-time step follows from the small-time upper bound, conservation
of mass, null cluster boundaries and compact right continuity. -/
theorem regularizedClusterExitTime_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (hright : ClusterCompactRightContinuityStmt.{u}) :
    RegularizedClusterExitTimeStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
  filter_upwards [hsmall.ae_eventually_dyadic, hμ,
    h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hright γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hsmallω hμω hop hmono hmass hnull hcont
  let _ : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  intro z hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz
  have hsmallz : ∃ t : ℝ, 0 < t ∧ closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
    obtain ⟨m, hm⟩ := hsmallω.exists
    refine ⟨(2 : ℝ)⁻¹ ^ m, by positivity, ?_⟩
    intro x hx
    have hbound := hm ((2 : ℝ)⁻¹ ^ m) ⟨by positivity, le_rfl⟩ z hz hx
    simp only [mem_ball] at hbound hz ⊢
    have htri := dist_triangle x z (0 : ℂ)
    norm_num at hbound
    linarith
  have hlarge : ∃ t : ℝ, 0 < t ∧ ¬ closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
    by_contra h
    have hall : ∀ t : ℝ, 0 < t → closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
      intro t ht
      by_contra hnot
      exact h ⟨t, ht, hnot⟩
    let M : ℝ := ((μ ω) (ball (0 : ℂ) 1)).toReal
    let t : ℝ := M + 1
    have ht : 0 < t := by dsimp [t, M]; have : 0 ≤ ((μ ω) (ball (0 : ℂ) 1)).toReal := ENNReal.toReal_nonneg; linarith
    have hb := hnull z hz1 t ht (hall t ht)
    have heq := (hmass 1 t (by norm_num) ht z hz1).2.2 (hall t ht) hb
    have hle : ENNReal.ofReal t ≤ (μ ω) (ball (0 : ℂ) 1) := by
      rw [← heq]
      exact measure_mono (fun x hx => hall t ht (subset_closure hx))
    have hfin : (μ ω) (ball (0 : ℂ) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hreal := ENNReal.toReal_mono hfin hle
    rw [ENNReal.toReal_ofReal ht.le] at hreal
    change t ≤ M at hreal
    dsimp [t] at hreal
    linarith
  have hpersist : ∀ t : ℝ, 0 < t → closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∃ t' : ℝ, t < t' ∧ closure (cluster (μ ω) 1 z t') ⊆ ball 0 1 := by
    intro t ht hin
    have hK : IsCompact (closure (cluster (μ ω) 1 z t)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_ball.subset hin)
    obtain ⟨ε, hε, hεsub⟩ := hK.exists_thickening_subset_open isOpen_ball hin
    obtain ⟨δ, hδ, hδbound⟩ := hcont z hz t ht hin ε hε
    refine ⟨t + δ / 2, by linarith, ?_⟩
    intro x hx
    apply hεsub
    have hxsum := hδbound (t + δ / 2) ⟨by linarith, by linarith⟩ hx
    obtain ⟨y, hy, w, hw, rfl⟩ := hxsum
    apply mem_thickening_iff.2
    refine ⟨y, subset_closure hy, ?_⟩
    simp only [mem_ball, dist_zero_right] at hw
    simpa only [dist_eq_norm, add_sub_cancel_left] using hw
  obtain ⟨T, hT, hbefore, hcontact⟩ := exists_exit_time_of_monotone
    (fun t ht => (hop t 1 ht (by norm_num) z hz1).1)
    (fun s hs t ht hst => hmono s t 1 hs hst (by norm_num) z hz1)
    (fun _ _ => cluster_subset_ball) hsmallz hlarge hpersist
  exact ⟨T, hT, hbefore, hcontact⟩

/-- Proposition 5.4 from the Section 3 cluster properties, null boundaries,
full support, and the bounds and continuity of Section 7. -/
theorem regularizedClusterHarmonicBalls_of_clusterProperties
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h72 : ClusterTimeContinuityStmt.{u}) : RegularizedClusterHarmonicBallsStmt.{u} := by
  have hright := clusterCompactRightContinuity_of_steps h33 h72
  exact regularizedClusterHarmonicBalls_of_exit h32 h33 h34
    (clusterShrinksToCenter_of_upperBound h71) h53 hfull h72
    (regularizedClusterExitTime_of_steps h32 h33 h34 h53 h71 hright)

end HarmonicBalls

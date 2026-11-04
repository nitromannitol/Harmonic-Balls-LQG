import HarmonicBalls.Proofs.Sec10.HoleExtinctionEndpoint

/-! # Remaining hole mass with boundary contact

At extinction, the original hole is covered by the closed cluster. Its
remaining mass is bounded by the remaining mass budget, even when the
cluster is no longer compactly contained in the unit disc.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A set covered by a later cluster closure, within the unit disc, has its
remaining mass bounded by the later cluster mass increment. -/
theorem measure_sdiff_cluster_closure_le_increment
    (μ : Measure ℂ) {z : ℂ} {s L : ℝ}
    (hopen : IsOpen (cluster μ 1 z s)) (hopenL : IsOpen (cluster μ 1 z L))
    (hmono : cluster μ 1 z s ⊆ cluster μ 1 z L)
    (hfin : μ (cluster μ 1 z s) ≠ ∞)
    (hnull : μ (frontier (cluster μ 1 z L) ∩ ball (0 : ℂ) 1) = 0)
    {U : Set ℂ} (hU : U ⊆ closure (cluster μ 1 z L))
    (hUdisc : U ⊆ ball (0 : ℂ) 1) :
    μ (U \ closure (cluster μ 1 z s)) ≤
      μ (cluster μ 1 z L) - μ (cluster μ 1 z s) := by
  calc
    μ (U \ closure (cluster μ 1 z s)) ≤
        μ ((cluster μ 1 z L \ cluster μ 1 z s) ∪
          (frontier (cluster μ 1 z L) ∩ ball (0 : ℂ) 1)) := by
      apply measure_mono
      intro x hx
      by_cases hxL : x ∈ cluster μ 1 z L
      · exact Or.inl ⟨hxL, fun hxs => hx.2 (subset_closure hxs)⟩
      · right
        refine ⟨?_, hUdisc hx.1⟩
        rw [frontier, hopenL.interior_eq]
        exact ⟨hU hx.1, hxL⟩
    _ ≤ μ (cluster μ 1 z L \ cluster μ 1 z s) +
        μ (frontier (cluster μ 1 z L) ∩ ball (0 : ℂ) 1) := measure_union_le _ _
    _ = μ (cluster μ 1 z L) - μ (cluster μ 1 z s) := by
      rw [hnull, add_zero, measure_sdiff hmono hopen.measurableSet.nullMeasurableSet hfin]

universe u

/-- Every initially compactly contained bounded hole has a finite lifetime.
For each earlier time, its remaining mass is bounded by the endpoint mass
budget minus the mass of the current cluster. At mass-saturating times this
is the remaining lifetime; endpoint compact containment is not assumed. -/
theorem ae_cluster_hole_remaining_mass_le_budget
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s → s < L →
          ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (∀ s : ℝ, L ≤ s →
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (∀ s : ℝ, t ≤ s → s ≤ L →
          μ ω (U \ closure (cluster (μ ω) 1 z s)) ≤
            ENNReal.ofReal L - μ ω (cluster (μ ω) 1 z s) ∧
          (μ ω (cluster (μ ω) 1 z s) = ENNReal.ofReal s →
            μ ω (U \ closure (cluster (μ ω) 1 z s)) ≤ ENNReal.ofReal (L - s))) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_extinction_at_lifetime_endpoint hI2 h611 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2) h611 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlife hopen hmono hmass hnull
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter, hcover, _⟩ := hlife t ht z hz hcl U hU hUb
  have hLpos := ht.trans htL
  have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure
      (hcl.trans ball_subset_closedBall) hU hUb
  refine ⟨L, htL, hbefore, hafter, ?_⟩
  intro s hts hsL
  have hs : 0 < s := ht.trans_le hts
  have hupper := (hmass 1 L zero_lt_one hLpos z hz).1
  have hfin : μ ω (cluster (μ ω) 1 z s) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmass 1 s zero_lt_one hs z hz).1
  have hinc := measure_sdiff_cluster_closure_le_increment (μ ω)
    (hopen s 1 hs zero_lt_one z hz).1 (hopen L 1 hLpos zero_lt_one z hz).1
    (hmono s L 1 hs hsL zero_lt_one z hz) hfin (hnull L hLpos z hz) hcover hUdisc
  refine ⟨hinc.trans (tsub_le_tsub_right hupper _), ?_⟩
  intro heq
  exact measure_sdiff_cluster_closure_le_of_subset_later_closure (μ ω) hs.le hsL
    (hopen s 1 hs zero_lt_one z hz).1 (hopen L 1 hLpos zero_lt_one z hz).1
    (hmono s L 1 hs hsL zero_lt_one z hz) heq hupper (hnull L hLpos z hz) hcover hUdisc

end HarmonicBalls

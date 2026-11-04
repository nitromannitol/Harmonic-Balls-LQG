import HarmonicBalls.Proofs.Sec10.HoleEndpointMass

/-! # Mass of a complementary component before extinction

If no descendant remains at a later time, the original component lies in the
later closed cluster. Mass conservation and nullity of the later frontier then
bound its mass by the elapsed time. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A complementary component with no descendant for a larger closed set is
contained in that larger set. -/
theorem complement_component_subset_of_no_descendant
    {K L U : Set ℂ} (hKL : K ⊆ L) (hU : U ∈ connectedComponentsIn Kᶜ)
    (hno : ¬ ∃ V ∈ connectedComponentsIn Lᶜ, V ⊆ U) : U ⊆ L := by
  intro x hxU
  by_contra hxL
  have hx : x ∈ Lᶜ := hxL
  let V := connectedComponentIn Lᶜ x
  have hxV : x ∈ V := mem_connectedComponentIn hx
  have hVsub : V ⊆ Kᶜ :=
    (connectedComponentIn_subset _ _).trans (compl_subset_compl.mpr hKL)
  obtain ⟨y, hy, hyU⟩ := hU
  have h := isPreconnected_connectedComponentIn.subset_connectedComponentIn hxV hVsub
  have hxUy : x ∈ connectedComponentIn Kᶜ y := hyU.symm ▸ hxU
  have heq : connectedComponentIn Kᶜ x = U := (connectedComponentIn_eq hxUy).symm.trans hyU
  exact hno ⟨V, ⟨x, hx, rfl⟩, heq ▸ h⟩

/-- If a cluster component has disappeared by a later time, its mass is at
most the elapsed time, provided the initial cluster has prescribed mass and
the later interior frontier is null. -/
theorem measure_cluster_hole_le_of_no_descendant
    (μ : Measure ℂ) {z : ℂ} {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (hopen : IsOpen (cluster μ 1 z t)) (hopen' : IsOpen (cluster μ 1 z s))
    (hmono : cluster μ 1 z t ⊆ cluster μ 1 z s)
    (hmass : μ (cluster μ 1 z t) = ENNReal.ofReal t)
    (hupper : μ (cluster μ 1 z s) ≤ ENNReal.ofReal s)
    (hnull : μ (frontier (cluster μ 1 z s) ∩ ball (0 : ℂ) 1) = 0)
    {U : Set ℂ} (hU : U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ)
    (hUdisc : U ⊆ ball (0 : ℂ) 1)
    (hno : ¬ ∃ V ∈ connectedComponentsIn (closure (cluster μ 1 z s))ᶜ, V ⊆ U) :
    μ U ≤ ENNReal.ofReal (s - t) := by
  have hcover := complement_component_subset_of_no_descendant (closure_mono hmono) hU hno
  obtain ⟨x, hx, hxeq⟩ := hU
  have hUsub : U ⊆ (closure (cluster μ 1 z t))ᶜ := by
    rw [← hxeq]
    exact connectedComponentIn_subset _ _
  have hincr := measure_cluster_sdiff_le_of_mass_eq μ 1 z ht hts hopen hmono hmass hupper
  calc
    μ U ≤ μ ((cluster μ 1 z s \ cluster μ 1 z t) ∪
        (frontier (cluster μ 1 z s) ∩ ball (0 : ℂ) 1)) := by
      apply measure_mono
      intro y hy
      by_cases hyC : y ∈ cluster μ 1 z s
      · exact Or.inl ⟨hyC, fun hyt => hUsub hy (subset_closure hyt)⟩
      · right
        refine ⟨?_, hUdisc hy⟩
        rw [frontier, hopen'.interior_eq]
        exact ⟨hcover hy, hyC⟩
    _ ≤ μ (cluster μ 1 z s \ cluster μ 1 z t) +
        μ (frontier (cluster μ 1 z s) ∩ ball (0 : ℂ) 1) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (s - t) := by rw [hnull, add_zero]; exact hincr

universe u

/-- Almost surely, a bounded hole at a mass-saturating time has mass at most
the elapsed time if it has no descendant at the later time. -/
theorem ae_cluster_hole_mass_le_of_no_descendant
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t s : ℝ, 0 < t → t ≤ s → ∀ z ∈ ball (0 : ℂ) 1,
      μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U →
      (¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) →
      μ ω U ≤ ENNReal.ofReal (s - t) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hmass hnull
  intro t s ht hts z hz heq U hU hUb hno
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  exact measure_cluster_hole_le_of_no_descendant (μ ω) ht.le hts
    (hopen t 1 ht zero_lt_one z hz).1
    (hopen s 1 (lt_of_lt_of_le ht hts) zero_lt_one z hz).1
    (hmono t s 1 ht hts zero_lt_one z hz) heq
    (hmass 1 s zero_lt_one (lt_of_lt_of_le ht hts) z hz).1
    (hnull s (lt_of_lt_of_le ht hts) z hz) hU
    (bounded_complement_component_subset_unit_ball isClosed_closure hcl hU hUb) hno

/-- If the lifetime endpoint remains compactly contained, every descendant
hole has mass at most the time remaining until extinction. -/
theorem ae_cluster_hole_mass_le_remaining_lifetime
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
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
        (∀ s : ℝ, L < s →
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (closure (cluster (μ ω) 1 z L) ⊆ ball 0 1 →
          ∀ s : ℝ, t ≤ s → s < L →
          ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          V ⊆ U → μ ω V ≤ ENNReal.ofReal (L - s)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_lifetime_endpoint_mass_deficit hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_hole_mass_le_of_no_descendant hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hlife hbound hmono hmass hnull
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter, hend⟩ := hlife t ht z hz hcl U hU hUb
  refine ⟨L, htL, hbefore, hafter, ?_⟩
  intro hclL s hts hsL V hV hVU
  have hs : 0 < s := ht.trans_le hts
  have hno : ¬ ∃ W ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z L))ᶜ, W ⊆ U := by
    intro hW
    exact (hend hW).2 hclL
  have hcls : closure (cluster (μ ω) 1 z s) ⊆ ball 0 1 :=
    (closure_mono (hmono s L 1 hs hsL.le zero_lt_one z hz)).trans hclL
  have hfront : μ ω (frontier (cluster (μ ω) 1 z s)) = 0 := by
    apply measure_mono_null _ (hnull s hs z hz)
    intro x hx
    exact ⟨hx, hcls (frontier_subset_closure hx)⟩
  have heq := (hmass 1 s zero_lt_one hs z hz).2.2 hcls hfront
  apply hbound s L hs hsL.le z hz heq V hV (hUb.subset hVU)
  rintro ⟨W, hW, hWV⟩
  exact hno ⟨W, hW, hWV.trans hVU⟩

end HarmonicBalls

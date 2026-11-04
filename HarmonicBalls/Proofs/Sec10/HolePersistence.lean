import HarmonicBalls.Proofs.Sec5.ContactMassContinuity
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec10.ExteriorComponent

/-! # Persistence of complementary holes

A hole containing a ball cannot disappear before enough mass has entered
that ball, provided the later cluster frontier is null inside the disc.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- If a ball in a complementary component has more mass than the elapsed
cluster time, a later complementary component still meets the ball and is
contained in the original component. -/
theorem cluster_complement_component_persists_of_ball_mass
    (μ : Measure ℂ) {z p : ℂ} {t s r : ℝ} (ht : 0 ≤ t) (hts : t ≤ s)
    (hopen : IsOpen (cluster μ 1 z t)) (hopen' : IsOpen (cluster μ 1 z s))
    (hmono : cluster μ 1 z t ⊆ cluster μ 1 z s)
    (hmass : μ (cluster μ 1 z t) = ENNReal.ofReal t)
    (hupper : μ (cluster μ 1 z s) ≤ ENNReal.ofReal s)
    (hnull : μ (frontier (cluster μ 1 z s) ∩ ball (0 : ℂ) 1) = 0)
    {U : Set ℂ} (hU : U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ)
    (hball : ball p r ⊆ U) (hdisc : ball p r ⊆ ball (0 : ℂ) 1)
    (hlower : ENNReal.ofReal (s - t) < μ (ball p r)) :
    ∃ V ∈ connectedComponentsIn (closure (cluster μ 1 z s))ᶜ,
      V ⊆ U ∧ (V ∩ ball p r).Nonempty := by
  have hincr := measure_cluster_sdiff_le_of_mass_eq μ 1 z ht hts hopen hmono hmass hupper
  have hUsub : U ⊆ (closure (cluster μ 1 z t))ᶜ := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact connectedComponentIn_subset _ _
  have hnot : ¬ ball p r ⊆ closure (cluster μ 1 z s) := by
    intro hsub
    have hsub' : ball p r ⊆
        (cluster μ 1 z s \ cluster μ 1 z t) ∪
          (frontier (cluster μ 1 z s) ∩ ball (0 : ℂ) 1) := by
      intro x hx
      by_cases hxD : x ∈ cluster μ 1 z s
      · exact Or.inl ⟨hxD, fun hxC => hUsub (hball hx) (subset_closure hxC)⟩
      · apply Or.inr
        refine ⟨?_, hdisc hx⟩
        rw [frontier, hopen'.interior_eq]
        exact ⟨hsub hx, hxD⟩
    have hbound : μ (ball p r) ≤ ENNReal.ofReal (s - t) := by
      calc
        μ (ball p r) ≤ μ ((cluster μ 1 z s \ cluster μ 1 z t) ∪
            (frontier (cluster μ 1 z s) ∩ ball (0 : ℂ) 1)) := measure_mono hsub'
        _ ≤ μ (cluster μ 1 z s \ cluster μ 1 z t) +
            μ (frontier (cluster μ 1 z s) ∩ ball (0 : ℂ) 1) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (s - t) := by rw [hnull, add_zero]; exact hincr
    exact (not_le_of_gt hlower) hbound
  obtain ⟨q, hqball, hqD⟩ := not_subset.mp hnot
  have hqU : q ∈ U := hball hqball
  have hqD' : q ∈ (closure (cluster μ 1 z s))ᶜ := hqD
  let V := connectedComponentIn (closure (cluster μ 1 z s))ᶜ q
  have hqV : q ∈ V := mem_connectedComponentIn hqD'
  have hcomp : V ∈ connectedComponentsIn (closure (cluster μ 1 z s))ᶜ := ⟨q, hqD', rfl⟩
  have hVsub : V ⊆ (closure (cluster μ 1 z t))ᶜ :=
    (connectedComponentIn_subset _ _).trans (compl_subset_compl.mpr (closure_mono hmono))
  have hVU : V ⊆ U := by
    obtain ⟨x, hx, rfl⟩ := hU
    have h := isPreconnected_connectedComponentIn.subset_connectedComponentIn hqV hVsub
    rw [connectedComponentIn_eq hqU]
    exact h
  exact ⟨V, hcomp, hVU, q, hqV, hqball⟩

universe u

/-- Under volume growth and the explicitly assumed Harnack and good-scale
estimates, a bounded hole containing an interior ball retains a bounded
complementary component until elapsed time reaches the ball's uniform
volume-growth lower bound. This does not assert that holes exist. -/
theorem ae_cluster_bounded_hole_persists_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ βm : ℝ, ∀ᵐ ω ∂P, 0 < βm ∧ ∃ r₀ > 0,
      ∀ t s : ℝ, 0 < t → t ≤ s → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ p : ℂ, ∀ r : ℝ, 0 < r → r < r₀ →
      ball p r ⊆ U → ball p r ⊆ ball 0 1 → s - t < r ^ βm →
      ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
        Bornology.IsBounded V ∧ V ⊆ U ∧ (V ∩ ball p r).Nonempty := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  refine ⟨βm, ?_⟩
  filter_upwards [hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2) h611 h82 γ α₀ hγ hγ2 hα
      Ω P hC hcirc μ hGFF hμ] with ω hV hopen hmono hmass hnull
  have hV1 := hV.2 1 zero_lt_one
  obtain ⟨r₀, hr₀, hvol⟩ := hV1.2.2
  refine ⟨hV1.1, r₀, hr₀, ?_⟩
  intro t s ht hts z hz hcl U hU hb p r hr hrr hball hdisc htime
  have hp : p ∈ ball (0 : ℂ) 1 := hdisc (mem_ball_self hr)
  have hsmall : ENNReal.ofReal (s - t) < μ ω (ball p r) :=
    ((ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hr βm)).mpr htime).trans_le
      (hvol r hr hrr p hp).1
  have hfront : μ ω (frontier (cluster (μ ω) 1 z t)) = 0 := by
    apply measure_mono_null _ (hnull t ht z hz)
    intro x hx
    exact ⟨hx, hcl (frontier_subset_closure hx)⟩
  have heq := (hmass 1 t zero_lt_one ht z hz).2.2 hcl hfront
  obtain ⟨V, hVc, hVU, hmeet⟩ := cluster_complement_component_persists_of_ball_mass
    (μ ω) ht.le hts (hopen t 1 ht zero_lt_one z hz).1
    (hopen s 1 (lt_of_lt_of_le ht hts) zero_lt_one z hz).1
    (hmono t s 1 ht hts zero_lt_one z hz) heq
    (hmass 1 s zero_lt_one (lt_of_lt_of_le ht hts) z hz).1
    (hnull s (lt_of_lt_of_le ht hts) z hz) hU hball hdisc hsmall
  exact ⟨V, hVc, hb.subset hVU, hVU, hmeet⟩

end HarmonicBalls

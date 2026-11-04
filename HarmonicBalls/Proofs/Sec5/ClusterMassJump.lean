import HarmonicBalls.Proofs.Sec5.VanishingIncrementContinuity
import HarmonicBalls.Proofs.Sec5.InteriorClusterBoundary

/-! # Cluster mass jumps and closed future intersections

Interior boundary nullity identifies the mass gained immediately after a
positive time with the mass of the new points in the closed future intersection.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal

/-- If each future set has null boundary in `U`, replacing a countable
intersection of these sets by their closures does not change its mass in `U`. -/
theorem measure_future_closure_sdiff_eq_measure_future_sdiff
    (μ : Measure ℂ) (U A : Set ℂ) (B : ℕ → Set ℂ)
    (hsub : ∀ n, B n ⊆ U) (hopen : ∀ n, IsOpen (B n))
    (hboundary : ∀ n, μ (frontier (B n) ∩ U) = 0) :
    μ (((⋂ n, closure (B n)) ∩ U) \ A) = μ ((⋂ n, B n) \ A) := by
  have hsmall : (⋂ n, B n) \ A ⊆ ((⋂ n, closure (B n)) ∩ U) \ A := by
    intro x hx
    exact ⟨⟨Set.mem_iInter.mpr (fun n => subset_closure (Set.mem_iInter.mp hx.1 n)),
      hsub 0 (Set.mem_iInter.mp hx.1 0)⟩, hx.2⟩
  have hnull : μ ((((⋂ n, closure (B n)) ∩ U) \ A) \ ((⋂ n, B n) \ A)) = 0 := by
    apply measure_mono_null _ (measure_iUnion_null hboundary)
    intro x hx
    have hxnot : x ∉ ⋂ n, B n := by
      intro h
      exact hx.2 ⟨h, hx.1.2⟩
    have hn : ∃ n, x ∉ B n := by simpa only [mem_iInter, not_forall] using hxnot
    obtain ⟨n, hn⟩ := hn
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_, hx.1.1.2⟩
    rw [frontier, (hopen n).interior_eq]
    exact ⟨Set.mem_iInter.mp hx.1.1.1 n, hn⟩
  exact (measure_eq_measure_of_null_sdiff hsmall hnull).symm

/-- For decreasing future open sets of finite measure, the increment masses
converge to the mass added in the closed future intersection within `U`. -/
theorem tendsto_measure_future_increment
    (μ : Measure ℂ) (U A : Set ℂ) (B : ℕ → Set ℂ)
    (hsub : ∀ n, B n ⊆ U) (hopen : ∀ n, IsOpen (B n))
    (hA : MeasurableSet A) (hanti : Antitone B) (hfinite : μ (B 0) ≠ ⊤)
    (hboundary : ∀ n, μ (frontier (B n) ∩ U) = 0) :
    Tendsto (fun n => μ (B n \ A)) atTop
      (𝓝 (μ (((⋂ n, closure (B n)) ∩ U) \ A))) := by
  have hanti' : Antitone (fun n => B n \ A) := fun _ _ hij => sdiff_subset_sdiff_left (hanti hij)
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun n => B n \ A) (fun n => ((hopen n).measurableSet.diff hA).nullMeasurableSet)
    hanti' ⟨0, ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)⟩
  have heq : (⋂ n, B n \ A) = (⋂ n, B n) \ A := by
    ext x
    simp only [mem_iInter, Set.mem_sdiff, forall_and]
    simp
  rw [heq, ← measure_future_closure_sdiff_eq_measure_future_sdiff μ U A B hsub hopen hboundary] at hlim
  exact hlim

universe u

/-- For every centre and positive time simultaneously, dyadic increment mass
converges to the mass of the new interior points in the future intersection. -/
theorem ae_tendsto_cluster_increment_mass_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      Tendsto (fun n : ℕ => μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t)) atTop
        (𝓝 (μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \ cluster (μ ω) 1 z t))) := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hmass hfront
  intro t ht z hz
  apply tendsto_measure_future_increment (μ ω) (ball 0 1) (cluster (μ ω) 1 z t)
    (fun n => cluster (μ ω) 1 z (t + dyadicScale n))
  · exact fun _ => cluster_subset_ball
  · exact fun n => (hopen (t + dyadicScale n) 1 (add_pos ht (dyadicScale_pos n)) zero_lt_one z hz).1
  · exact (hopen t 1 ht zero_lt_one z hz).1.measurableSet
  · intro i j hij
    apply hmono _ _ 1 (add_pos ht (dyadicScale_pos j)) _ zero_lt_one z hz
    have hs : dyadicScale j ≤ dyadicScale i := by
      dsimp [dyadicScale]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
    linarith
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hmass 1 (t + dyadicScale 0) zero_lt_one (add_pos ht (dyadicScale_pos 0)) z hz).1
  · intro n
    exact hfront (t + dyadicScale n) (add_pos ht (dyadicScale_pos n)) z hz

/-- Right-continuity of the cluster forces its dyadic increment masses to
converge to zero, even if the unit circle itself has positive measure. -/
theorem ae_vanishing_cluster_increment_of_right_continuity
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε) →
      Tendsto (fun n : ℕ => μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t)) atTop (𝓝 0) := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_tendsto_cluster_increment_mass_of_steps h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hfront hlim
  intro t ht z hz hright
  have hsub := (cluster_closure_dyadic_iInter_subset_iff_right_continuous ht
    (fun s s' hs hss => hmono s s' 1 hs hss zero_lt_one z hz)).2 hright
  have hnull : μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \ cluster (μ ω) 1 z t) = 0 := by
    apply measure_mono_null _ (hfront t ht z hz)
    intro x hx
    refine ⟨?_, hx.1.2⟩
    rw [frontier, (hopen t 1 ht zero_lt_one z hz).1.interior_eq]
    refine ⟨?_, hx.2⟩
    apply hsub
    simpa only [dyadicScale] using hx.1.1
  simpa only [hnull] using hlim t ht z hz

/-- If the future closed clusters introduce no new circle points, right
continuity is equivalent to the absence of an immediate mass increment. -/
theorem ae_cluster_right_continuity_iff_vanishing_increment_of_sphere_inclusion
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ sphere 0 1 ⊆
        closure (cluster (μ ω) 1 z t)) →
      ((∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε) ↔
      Tendsto (fun n : ℕ => μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t)) atTop (𝓝 0)) := by
  filter_upwards [ae_vanishing_cluster_increment_of_right_continuity h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_cluster_right_continuity_of_vanishing_increment_and_sphere_inclusion
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hforward hreverse
  intro t ht z hz hsphere
  constructor
  · exact hforward t ht z hz
  · intro hlim
    apply hreverse t ht z hz _ hsphere
    intro ε hε
    obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
    exact ⟨n, hn.le⟩

/-- For LQG clusters, the future closed intersection has no new interior
points precisely when the mass of its new interior points vanishes. -/
theorem ae_future_closure_inter_ball_subset_iff_measure_zero
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
        closure (cluster (μ ω) 1 z t)) ↔
      μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \ cluster (μ ω) 1 z t) = 0 := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_tendsto_cluster_increment_mass_of_steps h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_of_vanishing_increment
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hopen hfront hlim hexclude
  intro t ht z hz
  constructor
  · intro hsub
    apply measure_mono_null _ (hfront t ht z hz)
    intro x hx
    refine ⟨?_, hx.1.2⟩
    rw [frontier, (hopen t 1 ht zero_lt_one z hz).1.interior_eq]
    exact ⟨hsub hx.1, hx.2⟩
  · intro hnull
    apply hexclude t ht z hz
    intro ε hε
    have hlim0 := hlim t ht z hz
    rw [hnull] at hlim0
    obtain ⟨n, hn⟩ := (hlim0.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
    exact ⟨n, hn.le⟩

end HarmonicBalls

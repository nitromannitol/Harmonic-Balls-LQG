import HarmonicBalls.Proofs.Sec5.InteriorTimeContinuity
import HarmonicBalls.Proofs.Sec5.ClusterMassLeftContinuity
import HarmonicBalls.Proofs.Sec5.NullBoundaryContact

/-! # Continuity of mass and interior clusters

The cluster mass is continuous in time even after boundary contact. On each
compact subset of the open disc the closed clusters are right-continuous in
the one-sided Hausdorff sense.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise ENNReal MeasureTheory

universe u

/-- For a monotone cluster family, convergence to zero of dyadic mass
increments yields continuity of its mass at a positive time. -/
theorem continuousAt_measure_cluster_of_vanishing_increment
    {μ : Measure ℂ} {r t : ℝ} {z : ℂ} (ht : 0 < t)
    (hopen : IsOpen (cluster μ r z t))
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ r z s ⊆ cluster μ r z s')
    (hlim : Tendsto (fun n : ℕ => μ (cluster μ r z (t + dyadicScale n) \
      cluster μ r z t)) atTop (𝓝 0)) :
    ContinuousAt (fun s : ℝ => μ (cluster μ r z s)) t := by
  have hseq : Tendsto (fun n : ℕ => μ (cluster μ r z (t + dyadicScale n)))
      atTop (𝓝 (μ (cluster μ r z t))) := by
    have h := (tendsto_const_nhds (x := μ (cluster μ r z t))).add hlim
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards with n
    have hsub := hmono t (t + dyadicScale n) ht (le_add_of_nonneg_right (dyadicScale_pos n).le)
    simpa only [union_eq_right.mpr hsub] using
      (measure_add_sdiff hopen.measurableSet.nullMeasurableSet (cluster μ r z (t + dyadicScale n)))
  have hright : Tendsto (fun s : ℝ => μ (cluster μ r z s)) (𝓝[≥] t)
      (𝓝 (μ (cluster μ r z t))) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact lt_of_lt_of_le ha (measure_mono (hmono t s ht hs))
    · intro a ha
      obtain ⟨n, hn⟩ := (hseq.eventually (Iio_mem_nhds ha)).exists
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (lt_add_of_pos_right t (dyadicScale_pos n)))]
        with s hs hsupper
      exact lt_of_le_of_lt
        (measure_mono (hmono s (t + dyadicScale n) (ht.trans_le hs) hsupper.le)) hn
  rw [ContinuousAt, ← nhdsLT_sup_nhdsGE, tendsto_sup]
  exact ⟨tendsto_measure_cluster_nhdsLT ht hmono, hright⟩

/-- Almost surely the mass of every unit-disc cluster is continuous at every
positive time, including after the cluster meets the boundary. -/
theorem ae_continuousAt_measure_cluster
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      ContinuousAt (fun s : ℝ => μ ω (cluster (μ ω) 1 z s)) t := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_tendsto_cluster_increment_mass_zero hI2 h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hlim
  intro z hz t ht
  exact continuousAt_measure_cluster_of_vanishing_increment ht
    (hopen t 1 ht zero_lt_one z hz).1
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz) (hlim t ht z hz)

/-- If a bounded monotone family has no new interior limit points, its later
members on a closed interior set are uniformly close to the present member. -/
theorem local_right_continuity_of_no_new_interior_points
    {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hinter : (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t))
    {K : Set ℂ} (hK : IsClosed K) (hKsub : K ⊆ ball 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (F s) ∩ K ⊆ F t + ball (0 : ℂ) ε := by
  let U := Kᶜ ∪ thickening ε (closure (F t))
  have hU : IsOpen U := hK.isOpen_compl.union isOpen_thickening
  have hUsub : (⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))) ⊆ U := by
    intro x hx
    by_cases hxK : x ∈ K
    · right
      apply closure_subset_thickening hε _
      exact subset_closure (hinter ⟨by simpa only [dyadicScale] using hx, hKsub hxK⟩)
    · exact Or.inl hxK
  obtain ⟨δ, hδ, hδsub⟩ :=
    eventually_closure_subset_open_of_iInter_subset ht hmono hbound hU hUsub
  refine ⟨δ, hδ, ?_⟩
  intro s hs x hx
  have hxU := hδsub s hs hx.1
  have hxthick : x ∈ thickening ε (closure (F t)) := hxU.resolve_left (by simpa using hx.2)
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hxthick
  obtain ⟨z, hz, hyz⟩ := Metric.mem_closure_iff.mp hy ((ε - dist x y) / 2) (by linarith)
  have hxz : dist x z < ε := by linarith [dist_triangle x y z]
  refine ⟨z, hz, x - z, ?_, by abel⟩
  simpa [mem_ball, dist_eq_norm] using hxz

/-- On every closed subset of the open unit disc, the future closed clusters
are uniformly close to the current cluster, for all centres and positive times. -/
theorem ae_cluster_local_right_continuity
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      ∀ K : Set ℂ, IsClosed K → K ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
          closure (cluster (μ ω) 1 z s) ∩ K ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  filter_upwards [h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hmono hinter
  intro z hz t ht K hK hKsub ε hε
  exact local_right_continuity_of_no_new_interior_points ht
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball) (hinter t ht z hz) hK hKsub hε

/-- The cluster mass and the real mass deficit are continuous throughout
positive time, for every pole simultaneously. -/
theorem ae_continuousOn_cluster_mass_and_deficit
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      ContinuousOn (fun s : ℝ => μ ω (cluster (μ ω) 1 z s)) (Ioi 0) ∧
      ContinuousOn (fun s : ℝ => s - (μ ω (cluster (μ ω) 1 z s)).toReal) (Ioi 0) := by
  filter_upwards [ae_continuousAt_measure_cluster hI2 h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hcont hmass
  intro z hz
  constructor
  · intro t ht
    exact (hcont z hz t ht).continuousWithinAt
  · intro t ht
    have hfinite : μ ω (cluster (μ ω) 1 z t) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmass 1 t zero_lt_one ht z hz).1
    have hreal : ContinuousAt (fun s : ℝ => (μ ω (cluster (μ ω) 1 z s)).toReal) t :=
      (ENNReal.tendsto_toReal hfinite).comp (hcont z hz t ht)
    exact (continuousAt_id.sub hreal).continuousWithinAt

/-- Any failure of right continuity adds a set of positive one-dimensional
Hausdorff measure on the unit circle. -/
theorem ae_right_discontinuity_has_positive_new_circle_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε) →
      0 < μH[1] (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩
        sphere 0 1) \ closure (cluster (μ ω) 1 z t)) := by
  filter_upwards [ae_tendsto_cluster_increment_mass_zero hI2 h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_cluster_right_continuity_of_vanishing_increment_and_null_boundary
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hlim hcont
  intro z hz t ht hfail
  apply pos_iff_ne_zero.mpr
  intro hnull
  apply hfail
  apply hcont t ht z hz _ hnull
  intro ε hε
  obtain ⟨n, hn⟩ := ((hlim t ht z hz).eventually
    (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
  exact ⟨n, hn.le⟩

end HarmonicBalls

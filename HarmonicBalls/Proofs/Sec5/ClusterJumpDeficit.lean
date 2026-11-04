import HarmonicBalls.Proofs.Sec5.ClusterMassJump

/-! # Immediate cluster growth and the mass deficit -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal

/-- The mass gained in a limiting future intersection, together with the
present cluster mass, is at most the current time. -/
theorem future_increment_mass_add_le_time
    (μ : Measure ℂ) (A X : Set ℂ) (B : ℕ → Set ℂ) (t : ℝ) (d : ℕ → ℝ)
    (hA : MeasurableSet A) (hsub : ∀ n, A ⊆ B n)
    (hlim : Tendsto (fun n => μ (B n \ A)) atTop (𝓝 (μ X)))
    (hd : Tendsto d atTop (𝓝 0))
    (hmass : ∀ n, μ (B n) ≤ ENNReal.ofReal (t + d n)) :
    μ X + μ A ≤ ENNReal.ofReal t := by
  have hleft : Tendsto (fun n => μ (B n \ A) + μ A) atTop (𝓝 (μ X + μ A)) :=
    hlim.add tendsto_const_nhds
  have hright : Tendsto (fun n => ENNReal.ofReal (t + d n)) atTop
      (𝓝 (ENNReal.ofReal t)) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.add hd)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro n
  have heq : B n ∩ A = A := Set.inter_eq_right.mpr (hsub n)
  have he := measure_sdiff_add_inter (μ := μ) (B n) hA
  rw [heq] at he
  rw [he]
  exact hmass n

universe u

/-- Almost surely, at every positive time, the mass of new interior points
in the closed future intersection is bounded by the current mass deficit. -/
theorem ae_future_increment_mass_add_le_time_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \
        cluster (μ ω) 1 z t) + μ ω (cluster (μ ω) 1 z t) ≤ ENNReal.ofReal t := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_tendsto_cluster_increment_mass_of_steps h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hmass hlim
  intro t ht z hz
  apply future_increment_mass_add_le_time (μ ω) (cluster (μ ω) 1 z t)
    (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \
      cluster (μ ω) 1 z t) (fun n => cluster (μ ω) 1 z (t + dyadicScale n))
    t dyadicScale
  · exact (hopen t 1 ht zero_lt_one z hz).1.measurableSet
  · intro n
    exact hmono t (t + dyadicScale n) 1 ht
      (le_add_of_nonneg_right (dyadicScale_pos n).le) zero_lt_one z hz
  · exact hlim t ht z hz
  · exact tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds
  · intro n
    exact (hmass 1 (t + dyadicScale n) zero_lt_one
      (add_pos ht (dyadicScale_pos n)) z hz).1

/-- A new interior future point forces a positive mass jump which persists
at every later time and is bounded by the present mass deficit. -/
theorem ae_interior_future_point_forces_mass_jump
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∃ x ∈ (⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1,
        x ∉ closure (cluster (μ ω) 1 z t)) →
      let J := μ ω (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1) \
        cluster (μ ω) 1 z t)
      0 < J ∧ (∀ s : ℝ, t < s → J ≤ μ ω (cluster (μ ω) 1 z s \
        cluster (μ ω) 1 z t)) ∧ J + μ ω (cluster (μ ω) 1 z t) ≤ ENNReal.ofReal t := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps h32 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_iff_measure_zero hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_increment_mass_add_le_time_of_steps h32 h33 h34 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hfront hiff hbound
  intro t ht z hz ⟨x, hx, hxnot⟩
  dsimp only
  refine ⟨?_, ?_, hbound t ht z hz⟩
  · apply pos_iff_ne_zero.mpr
    intro hzero
    exact hxnot ((hiff t ht z hz).2 hzero hx)
  · intro s hts
    have hsmall : ∀ᶠ n : ℕ in atTop, dyadicScale n < s - t :=
      tendsto_dyadicScale_nhdsGT
        (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (sub_pos.mpr hts)))
    obtain ⟨n, hn⟩ := hsmall.exists
    rw [measure_future_closure_sdiff_eq_measure_future_sdiff (μ ω) (ball 0 1)
      (cluster (μ ω) 1 z t) (fun n => cluster (μ ω) 1 z (t + dyadicScale n))
      (fun _ => cluster_subset_ball)
      (fun n => (hopen (t + dyadicScale n) 1 (add_pos ht (dyadicScale_pos n))
        zero_lt_one z hz).1)
      (fun n => hfront (t + dyadicScale n) (add_pos ht (dyadicScale_pos n)) z hz)]
    apply measure_mono
    apply sdiff_subset_sdiff_left
    intro y hy
    apply hmono (t + dyadicScale n) s 1 (add_pos ht (dyadicScale_pos n))
      (by linarith) zero_lt_one z hz
    exact Set.mem_iInter.mp hy n

end HarmonicBalls

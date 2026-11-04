import HarmonicBalls.Proofs.Sec8.ClusterBoundary

/-!
# Interior boundary mass of a cluster

The good-scale and Harnack argument applies inside the domain even when the
cluster reaches its boundary. This isolates the unit circle as the remaining
possible contribution to the boundary mass.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- The good-scale argument makes the part of the cluster boundary inside the
unit disc null, without requiring the closure to stay inside the disc. -/
theorem measure_frontier_cluster_inter_ball_eq_zero_of_good_scales_and_component_harnack
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (t : ℝ)
    (hs : IsOpen (cluster μ 1 z t)) (hz : z ∈ ball (0 : ℂ) 1)
    (βminus : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m α ζ : ℝ)
    (hm : 0 < m) (hα : 0 < α) (hζ : ζ < 1)
    (hcount : ∀ᵐ w ∂μ.restrict (ball (0 : ℂ) 1), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        veryGoodComparableScaleCount μ βminus w N₀ a b C₁m C₁p C₂m C₂p C₃ m N)
    (hcomponent : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ ball (0 : ℂ) 1,
      closedBall w ρ ⊆ ball 0 1 \ {z} →
      IsVeryGoodAnnulus μ βminus ρ w N₀ a b C₁m C₁p C₂m C₂p C₃ →
      ∀ Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball w ρ),
        μ (Λ ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
        Λ ∩ closedBall w (ρ / 2) = ∅) :
    μ (frontier (cluster μ 1 z t) ∩ ball 0 1) = 0 := by
  apply ae_restrict_eq_bot.1
  apply Filter.eventually_false_iff_eq_bot.1
  have hcount' := (ae_mono (Measure.restrict_mono_set μ (inter_subset_right :
    frontier (cluster μ 1 z t) ∩ ball 0 1 ⊆ ball 0 1))) hcount
  have hdensity := (ae_mono (Measure.restrict_mono_set μ (inter_subset_left :
    frontier (cluster μ 1 z t) ∩ ball 0 1 ⊆ frontier (cluster μ 1 z t))))
      (ae_eventually_measure_inter_dyadicBall_le_on_frontier μ hs α m hα hm)
  filter_upwards [hcount', hdensity,
    ae_restrict_mem (isClosed_frontier.measurableSet.inter measurableSet_ball)]
    with w hwcount hwdensity ⟨hwfront, hwball⟩
  have hwne : w ≠ z := by
    intro hwz
    subst w
    exact (disjoint_frontier_iff_isOpen.2 hs).le_bot ⟨hwfront, self_mem_cluster hz⟩
  have hwu : w ∈ ball (0 : ℂ) 1 \ {z} := ⟨hwball, by simpa using hwne⟩
  have hu : ball (0 : ℂ) 1 \ {z} ∈ 𝓝 w :=
    (isOpen_ball.sdiff isClosed_singleton).mem_nhds hwu
  have hsmall : ∀ᶠ n : ℕ in atTop, dyadicScale n < 1 :=
    tendsto_dyadicScale_nhdsGT (eventually_nhdsWithin_of_eventually_nhds
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1 hwdensity
  obtain ⟨K₂, hK₂⟩ := Filter.eventually_atTop.1
    ((eventually_dyadic_closedBall_subset hu).and hsmall)
  obtain ⟨n, hn, hv, hc⟩ :=
    exists_veryGoodComparableScale_ge_of_count μ βminus w N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
      hζ hwcount (max K₁ K₂)
  have hmass := measure_inter_annulus_le_of_ball_comparison μ (cluster μ 1 z t) w n α m hc
    (hK₁ n (le_trans (le_max_left _ _) hn))
  have hdyad : dyadicScale (n + 1) = dyadicScale n / 2 := by
    simp only [dyadicScale, pow_succ]
    ring
  rw [hdyad] at hmass
  obtain ⟨hnball, hn1⟩ := hK₂ n (le_trans (le_max_right _ _) hn)
  have hdisjoint := inter_ball_eq_empty_of_component_harnack μ _ w _ α (dyadicScale_pos n)
    (hcomponent _ ⟨dyadicScale_pos n, hn1⟩ w hwball hnball hv) hmass
  exact not_mem_closure_of_disjoint_ball (half_pos (dyadicScale_pos n)) hdisjoint
    (frontier_subset_closure hwfront)

/-- Absolute continuity transfers interior boundary nullity to the residual
measure in the Laplacian decomposition. -/
theorem measure_frontier_cluster_inter_ball_eq_zero_of_absolutelyContinuous
    (μ ν : Measure ℂ) (z : ℂ) (t : ℝ)
    (hν : ν.restrict (ball (0 : ℂ) 1) ≪ μ.restrict (ball (0 : ℂ) 1))
    (hinterior : μ (frontier (cluster μ 1 z t) ∩ ball 0 1) = 0) :
    ν (frontier (cluster μ 1 z t) ∩ ball 0 1) = 0 := by
  have h := hν (s := frontier (cluster μ 1 z t)) (by
    rw [Measure.restrict_apply isClosed_frontier.measurableSet]
    exact hinterior)
  rwa [Measure.restrict_apply isClosed_frontier.measurableSet] at h

/-- A null unit circle upgrades interior boundary nullity to global boundary
nullity, since the closure of the cluster is contained in the closed disc. -/
theorem measure_frontier_cluster_eq_zero_of_inter_ball_and_sphere
    (μ : Measure ℂ) (z : ℂ) (t : ℝ)
    (hinterior : μ (frontier (cluster μ 1 z t) ∩ ball 0 1) = 0)
    (hsphere : μ (sphere (0 : ℂ) 1) = 0) :
    μ (frontier (cluster μ 1 z t)) = 0 := by
  apply measure_mono_null _ (measure_union_null hinterior hsphere)
  intro w hw
  by_cases hball : w ∈ ball (0 : ℂ) 1
  · exact Or.inl ⟨hw, hball⟩
  · apply Or.inr
    have hclosed : w ∈ closedBall (0 : ℂ) 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
        (frontier_subset_closure hw)
    rw [mem_closedBall] at hclosed
    rw [mem_ball] at hball
    rw [mem_sphere]
    exact le_antisymm hclosed (le_of_not_gt hball)

universe u

/-- Conditionally on the Section 3, 6 and 8 estimates, all positive-time
clusters have null boundary inside the disc, including at boundary contact. -/
theorem ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      μ ω (frontier (cluster (μ ω) 1 z t) ∩ ball 0 1) = 0 := by
  let β : ℝ := (2 + γ) ^ 2 / 2 + 1
  have hβ : (2 + γ) ^ 2 / 2 < β := by dsimp [β]; linarith
  obtain ⟨C₃, hC₃, h82⟩ := h82 γ α₀ hγ hγ2 hα₀ β hβ
  obtain ⟨b, hb, N₁f, αf, hN₁f, h611⟩ := h611 γ hγ hγ2 β hβ C₃ hC₃
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, h82⟩ :=
    h82 (1 / 2) (by norm_num) b hb
  let N₀ := max N₁ (N₁f a C₁m C₂p)
  have hN₀ : N₁f a C₁m C₂p ≤ N₀ := le_max_right _ _
  have hα := (hN₁f a ha C₁m C₂p h1m h2p).2 N₀ hN₀
  obtain ⟨m, hm, h82⟩ := h82 N₀ (le_max_left _ _)
  filter_upwards [hμ, h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h611 α₀ hα₀ Ω P hC hcirc μ hGFF hμ, h82 Ω P hC hcirc μ hGFF hμ]
    with ω hfinite hopen hharnack hgood
  let : IsLocallyFiniteMeasure (μ ω) := hfinite.isLocallyFiniteMeasure
  intro t ht z hz
  apply measure_frontier_cluster_inter_ball_eq_zero_of_good_scales_and_component_harnack
    (μ ω) z t (hopen t 1 ht (by norm_num) z hz).1 hz
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m (αf a N₀ C₁m) (1 / 2) hm hα.1 (by norm_num) hgood
  exact hharnack a ha C₁m C₁p C₂m C₂p h1m h1p h2m h2p N₀ hN₀ z hz t ht

end HarmonicBalls

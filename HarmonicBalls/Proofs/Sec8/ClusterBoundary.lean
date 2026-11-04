import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import HarmonicBalls.Proofs.Sec8.BoundaryDensity
import HarmonicBalls.Draft.Section6
import HarmonicBalls.Draft.Section8
import HarmonicBalls.Draft.Section3

/-!
# Boundary of a cluster from good annuli

The local Harnack estimate applies to connected components. At each boundary
point, sufficiently small annuli avoid the pole and remain in the domain.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- Component-wise Harnack exclusion implies exclusion for the whole set. -/
theorem inter_ball_eq_empty_of_component_harnack
    (μ : Measure ℂ) (s : Set ℂ) (w : ℂ) (ρ α : ℝ) (hρ : 0 < ρ)
    (hcomponent : ∀ Λ ∈ connectedComponentsIn (s ∩ ball w ρ),
      μ (Λ ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      Λ ∩ closedBall w (ρ / 2) = ∅)
    (hmass : μ (s ∩ annulus w (ρ / 2) ρ) ≤
      ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ)) :
    s ∩ ball w (ρ / 2) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
  have hyρ : y ∈ s ∩ ball w ρ :=
    ⟨hy.1, ball_subset_ball (by linarith) hy.2⟩
  set Λ := connectedComponentIn (s ∩ ball w ρ) y
  have hΛ : Λ ∈ connectedComponentsIn (s ∩ ball w ρ) := ⟨y, hyρ, rfl⟩
  have hΛsub : Λ ⊆ s := fun x hx => (connectedComponentIn_subset _ _ hx).1
  have hΛmass : μ (Λ ∩ annulus w (ρ / 2) ρ) ≤
      ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) :=
    (measure_mono (inter_subset_inter_left _ hΛsub)).trans hmass
  have h0 := hcomponent Λ hΛ hΛmass
  exact (eq_empty_iff_forall_notMem.1 h0) y ⟨mem_connectedComponentIn hyρ, ball_subset_closedBall hy.2⟩

/-- Dyadic closed balls eventually lie inside any open neighbourhood of the centre. -/
theorem eventually_dyadic_closedBall_subset {w : ℂ} {u : Set ℂ} (hu : u ∈ 𝓝 w) :
    ∀ᶠ n : ℕ in atTop, closedBall w (dyadicScale n) ⊆ u := by
  exact tendsto_dyadicScale_nhdsGT.eventually
    (eventually_nhdsWithin_of_eventually_nhds (eventually_closedBall_subset hu))

/-- The deterministic part of Proposition 8.1, using the component form of
Lemma 6.11 and the typical-point count of Lemma 8.2. -/
theorem measure_frontier_cluster_eq_zero_of_good_scales_and_component_harnack
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (t : ℝ)
    (hs : IsOpen (cluster μ 1 z t)) (hz : z ∈ ball (0 : ℂ) 1)
    (hclosure : closure (cluster μ 1 z t) ⊆ ball 0 1)
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
    μ (frontier (cluster μ 1 z t)) = 0 := by
  apply measure_frontier_eq_zero_of_good_scales_and_harnack μ hs βminus N₀ a b C₁m C₁p C₂m C₂p C₃ m α ζ hm hα hζ
  · exact (ae_mono (Measure.restrict_mono_set μ (frontier_subset_closure.trans hclosure))) hcount
  · filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with w hw
    have hwball : w ∈ ball (0 : ℂ) 1 := hclosure (frontier_subset_closure hw)
    have hwne : w ≠ z := by
      intro hwz
      subst w
      exact (disjoint_frontier_iff_isOpen.2 hs).le_bot ⟨hw, self_mem_cluster hz⟩
    have hwu : w ∈ ball (0 : ℂ) 1 \ {z} := ⟨hwball, by simpa using hwne⟩
    have hu : ball (0 : ℂ) 1 \ {z} ∈ 𝓝 w :=
      (isOpen_ball.sdiff isClosed_singleton).mem_nhds hwu
    have hsmall : ∀ᶠ n : ℕ in atTop, dyadicScale n < 1 :=
      tendsto_dyadicScale_nhdsGT (eventually_nhdsWithin_of_eventually_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    filter_upwards [eventually_dyadic_closedBall_subset hu, hsmall] with n hn hn1 hv hmass
    have hdyad : dyadicScale (n + 1) = dyadicScale n / 2 := by
      simp only [dyadicScale, pow_succ]
      ring
    rw [hdyad] at hmass
    exact inter_ball_eq_empty_of_component_harnack μ _ w _ α (dyadicScale_pos n)
      (hcomponent _ ⟨dyadicScale_pos n, hn1⟩ w hwball hn hv) hmass

universe u

/-- Proposition 8.1 follows from the cluster regularity, the component-wise
Harnack estimate and the typical-point good-scale estimate. -/
theorem boundaryMeasureZeroOfCompactClusterStmt_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀
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
  intro Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hμ, h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h611 α₀ hα₀ Ω P hC hcirc μ hGFF hμ, h82 Ω P hC hcirc μ hGFF hμ]
    with ω hfinite hopen hharnack hgood
  let : IsLocallyFiniteMeasure (μ ω) := hfinite.isLocallyFiniteMeasure
  intro t ht z hz hclosure
  apply measure_frontier_cluster_eq_zero_of_good_scales_and_component_harnack
    (μ ω) z t (hopen t 1 ht (by norm_num) z hz).1 hz hclosure
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m (αf a N₀ C₁m) (1 / 2) hm hα.1 (by norm_num) hgood
  exact hharnack a ha C₁m C₁p C₂m C₂p h1m h1p h2m h2p N₀ hN₀ z hz t ht

end HarmonicBalls

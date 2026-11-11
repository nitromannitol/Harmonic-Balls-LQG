import HarmonicBalls.Proofs.Sec5.QuantitativeBoundaryJump
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Summability of boundary jumps

The total separations of distinct immediate jumps are bounded by the length
of the boundary circle. This is conditional on exclusion of new interior
points; it does not exclude boundary jumps.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped BigOperators ENNReal MeasureTheory

/-- The separations at finitely many distinct times sum to at most the
circumference of the unit circle. -/
theorem sum_separated_future_points_le
    {ι : Type*} (F : ℝ → Set ℂ) (times : ι → ℝ) (points : ι → ℂ)
    (d : ι → ℝ) (S : Finset ι) (htimes : Function.Injective times)
    (ht : ∀ i ∈ S, 0 < times i) (hd : ∀ i ∈ S, 0 ≤ d i)
    (hx : ∀ i ∈ S, points i ∈ ⋂ n : ℕ, closure (F (times i + dyadicScale n)))
    (hdis : ∀ i ∈ S, Disjoint (ball (points i) (d i)) (closure (F (times i))))
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hconnected : ∀ s, 0 < s → IsPreconnected (closure (F s)))
    (hne : ∀ s, 0 < s → (F s).Nonempty)
    (hinter : ∀ t, 0 < t →
      (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t)) :
    ∑ i ∈ S, d i ≤ 2 * Real.pi := by
  classical
  obtain ⟨b, hb⟩ := (S.image times).bddAbove
  let T := b + 1
  have hS : ∀ t ∈ S.image times, 0 < t ∧ t < T := by
    intro t ht'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht'
    exact ⟨ht i hi, by have := hb (Finset.mem_image.mpr ⟨i, hi, rfl⟩); dsimp [T]; linarith⟩
  let J : ℝ → ℝ≥0∞ := fun t =>
    μH[1] (((⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ sphere 0 1) \ closure (F t))
  have hsum : (∑ i ∈ S, J (times i)) ≤ ENNReal.ofReal (2 * Real.pi) := by
    rw [← Finset.sum_image (fun i _ j _ hij => htimes hij)]
    exact sum_measure_boundary_future_jumps_le (fun t => closure (F t)) T (S.image times) hS
      (fun _ => isClosed_closure) (fun _ _ ha hab => closure_mono (hmono _ _ ha hab))
  have hsep : ∀ i ∈ S, ENNReal.ofReal (d i) ≤ J (times i) := by
    intro i hi
    obtain ⟨z, hz⟩ := hne (times i) (ht i hi)
    exact ofReal_le_boundary_future_jump_of_separated_point (ht i hi) hz hmono hbound
      hconnected (hinter _ (ht i hi)) (hx i hi) (hdis i hi)
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2 * Real.pi)).mp
  rw [ENNReal.ofReal_sum_of_nonneg hd]
  exact (Finset.sum_le_sum hsep).trans hsum

/-- Along any injective family of positive times, separated immediate jumps
have summable separations and total separation at most `2π`. -/
theorem summable_separated_future_points
    {ι : Type*} (F : ℝ → Set ℂ) (times : ι → ℝ) (points : ι → ℂ) (d : ι → ℝ)
    (htimes : Function.Injective times) (ht : ∀ i, 0 < times i) (hd : ∀ i, 0 ≤ d i)
    (hx : ∀ i, points i ∈ ⋂ n : ℕ, closure (F (times i + dyadicScale n)))
    (hdis : ∀ i, Disjoint (ball (points i) (d i)) (closure (F (times i))))
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hconnected : ∀ s, 0 < s → IsPreconnected (closure (F s)))
    (hne : ∀ s, 0 < s → (F s).Nonempty)
    (hinter : ∀ t, 0 < t →
      (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t)) :
    Summable d ∧ (∑' i, d i) ≤ 2 * Real.pi := by
  have hsum : ∀ S : Finset ι, ∑ i ∈ S, d i ≤ 2 * Real.pi := by
    intro S
    exact sum_separated_future_points_le F times points d S htimes
      (fun i _ => ht i) (fun i _ => hd i) (fun i _ => hx i) (fun i _ => hdis i)
      hmono hbound hconnected hne hinter
  exact ⟨summable_of_sum_le hd hsum, Real.tsum_le_of_sum_le hd hsum⟩

/-- The distances of selected future points to the present closed clusters
are summable over any injective family of positive times. -/
theorem summable_infDist_future_points
    {ι : Type*} (F : ℝ → Set ℂ) (times : ι → ℝ) (points : ι → ℂ)
    (htimes : Function.Injective times) (ht : ∀ i, 0 < times i)
    (hx : ∀ i, points i ∈ ⋂ n : ℕ, closure (F (times i + dyadicScale n)))
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1)
    (hconnected : ∀ s, 0 < s → IsPreconnected (closure (F s)))
    (hne : ∀ s, 0 < s → (F s).Nonempty)
    (hinter : ∀ t, 0 < t →
      (⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ ball 0 1 ⊆ closure (F t)) :
    Summable (fun i => infDist (points i) (closure (F (times i)))) ∧
      (∑' i, infDist (points i) (closure (F (times i)))) ≤ 2 * Real.pi := by
  exact summable_separated_future_points F times points
    (fun i => infDist (points i) (closure (F (times i)))) htimes ht
    (fun _ => infDist_nonneg) hx (fun _ => disjoint_ball_infDist)
    hmono hbound hconnected hne hinter

universe u

/-- Almost surely, for every pole and every sequence of distinct positive
times, distances of selected future points from current clusters sum to at
most the unit-circle circumference. -/
theorem ae_summable_infDist_cluster_future_points
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ (times : ℕ → ℝ) (points : ℕ → ℂ),
      Function.Injective times → (∀ i, 0 < times i) →
      (∀ i, points i ∈ ⋂ n : ℕ,
        closure (cluster (μ ω) 1 z (times i + dyadicScale n))) →
      Summable (fun i => infDist (points i) (closure (cluster (μ ω) 1 z (times i)))) ∧
      (∑' i, infDist (points i) (closure (cluster (μ ω) 1 z (times i)))) ≤ 2 * Real.pi := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hinter
  intro z hz times points htimes ht hx
  apply summable_infDist_future_points (fun t => cluster (μ ω) 1 z t) times points htimes ht hx
  · exact fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz
  · exact fun _ _ => cluster_subset_ball
  · exact fun s hs => (hopen s 1 hs zero_lt_one z hz).2.1.isPreconnected.closure
  · exact fun _ _ => ⟨z, self_mem_cluster hz⟩
  · exact fun t ht' => hinter t ht' z hz


end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.RegularizedMeasure
import HarmonicBalls.Steps.Sec5.ClusterContinuity
import HarmonicBalls.Draft.Section3

/-!
# Proposition 5.4 from exit time and Hausdorff continuity

The proof separates the exit-time assertion and two-sided Hausdorff
continuity (GRAPH G7) from the mass and geometric assertions. The latter
follow from Sections 3 and 5 and the regularization lemmas.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Positive exit time, compact containment before exit, and boundary
contact at exit in Proposition 5.4. -/
def RegularizedClusterExitTimeStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Ioo 0 T, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1) ∧
      (closure (regularizedCluster (μ ω) 1 z T) ∩ sphere (0 : ℂ) 1).Nonempty

/-- Two-sided Hausdorff continuity of the regularized clusters before exit.
Proposition 7.2 covers right continuity; left continuity is GRAPH G7. -/
def RegularizedClusterHausdorffContinuityStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ T : ℝ, 0 < T →
      (∀ t ∈ Ioo 0 T, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1) →
      HausdorffContinuousOn (regularizedCluster (μ ω) 1 z) (Ioo 0 T)

/-- Proposition 5.4 from its exit-time and continuity steps, together with
cluster openness, monotonicity, mass conservation, shrinking and null boundary. -/
theorem regularizedClusterHarmonicBalls_of_steps
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (hshrink : ClusterShrinksToCenterStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (hexit : RegularizedClusterExitTimeStep.{u})
    (hcont : RegularizedClusterHausdorffContinuityStep.{u}) : RegularizedClusterHarmonicBallsStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hshrink γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hexit γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hcont γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hop hmono hmass hsmall hboundary he hc
  intro z hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz
  obtain ⟨T, hT, hcompact, hcontact⟩ := he z hz
  have hcluster : ∀ t ∈ Ioo (0 : ℝ) T, IsOpen (cluster (μ ω) 1 z t) ∧
      IsConnected (cluster (μ ω) 1 z t) := by
    intro t ht
    exact ⟨(hop t 1 ht.1 (by norm_num) z hz1).1, (hop t 1 ht.1 (by norm_num) z hz1).2.1⟩
  have hnull : ∀ t ∈ Ioo (0 : ℝ) T, μ ω (frontier (cluster (μ ω) 1 z t)) = 0 :=
    fun t ht => hboundary z hz1 t ht.1 (hcompact t ht)
  refine ⟨T, hT, ?_, ?_, hcontact⟩
  · intro t ht
    exact (closure_minimal interior_subset isClosed_closure).trans (hcompact t ht)
  · refine {
      measure_eq := ?_
      measure_frontier := ?_
      isRegularOpen := ?_
      isBounded := ?_
      isConnected := ?_
      mem := ?_
      monotoneOn := ?_
      hausdorffContinuousOn := hc z hz T hT hcompact
      iInter_eq := ?_ }
    · intro t ht
      rw [measure_regularizedCluster_eq (hcluster t ht).1 (hnull t ht)]
      exact (hmass 1 t (by norm_num) ht.1 z hz1).2.2 (hcompact t ht) (hnull t ht)
    · intro t ht
      exact measure_frontier_regularizedCluster_eq_zero (hcluster t ht).1 (hnull t ht)
    · intro t ht
      exact isRegularOpen_regularizedCluster _ _ _ _
    · intro t ht
      apply isBounded_regularizedCluster
      exact isBounded_ball.subset (fun x hx => (subset_closure hx |> hcompact t ht))
    · intro t ht
      exact isConnected_regularizedCluster (hcluster t ht).1 (hcluster t ht).2
    · intro t ht
      apply cluster_subset_regularizedCluster (hcluster t ht).1
      exact mem_cluster_iff.2 ⟨hz1, Or.inl rfl⟩
    · intro s hs t ht hst
      exact regularizedCluster_subset_of_cluster_subset (hmono s t 1 hs.1 hst (by norm_num) z hz1)
    · apply Subset.antisymm
      · intro x hx
        have hx' : x ∈ ⋂ t ∈ Ioi (0 : ℝ), closure (cluster (μ ω) 1 z t) := by
          simp only [mem_iInter, mem_Ioi] at hx ⊢
          intro t ht
          by_cases htT : t < T
          · exact interior_subset (hx t ⟨ht, htT⟩)
          · have hhalf : T / 2 ∈ Ioo (0 : ℝ) T := ⟨half_pos hT, half_lt_self hT⟩
            have hle : T / 2 ≤ t := le_trans hhalf.2.le (not_lt.1 htT)
            have hsub := hmono (T / 2) t 1 hhalf.1 hle (by norm_num) z hz1
            exact closure_mono hsub (interior_subset (hx (T / 2) hhalf))
        simpa only [hsmall z hz] using hx'
      · intro x hx
        rw [mem_singleton_iff] at hx
        subst x
        simp only [mem_iInter]
        intro t ht
        apply cluster_subset_regularizedCluster (hcluster t ht).1
        exact mem_cluster_iff.2 ⟨hz1, Or.inl rfl⟩

end HarmonicBalls

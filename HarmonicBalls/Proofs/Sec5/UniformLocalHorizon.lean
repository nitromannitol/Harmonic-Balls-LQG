import HarmonicBalls.Proofs.Sec5.HorizonPositivity
import HarmonicBalls.Proofs.Sec5.IntervalRestriction

/-! # Uniform local intervals from a countable family of centres -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set ProbabilityTheory TopologicalSpace Filter

/-- A countable-centre coverage property turns Proposition 5.4 into a
measurable positive horizon simultaneously valid at all centres in `B(0,1/2)`.
The coverage property and fixed-centre measurability remain explicit. -/
theorem uniformLocalHorizon_of_countableCentres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (hfam : ClusterFamilyMeasurabilityStep.{u})
    {ι : Type*} [Countable ι] (e : ι → {z // z ∈ ball (0 : ℂ) (1 / 2)})
    (hcover : ∀ᵐ ω ∂P, ∀ (j : {z // z ∈ ball (0 : ℂ) (1 / 2)}) (t : Ioi (0 : ℝ)),
      cluster (μ ω) 1 j t ⊆ closure (⋃ i, cluster (μ ω) 1 (e i) t)) :
    ∃ H : Ω → ℝ, AEMeasurable H P ∧ ∀ᵐ ω ∂P, 0 < H ω ∧
      ∀ z ∈ ball (0 : ℂ) (1 / 2),
        SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z (H ω) ∧
        ∀ t ∈ Ioo 0 (H ω), closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ∧
          μ ω (frontier (cluster (μ ω) 1 z t)) = 0 := by
  let H : Ω → ℝ := fun ω => realDenseSequenceBallHorizon (3 / 4)
    (fun i t => cluster (μ ω) 1 (e i) t)
  let e' : ι → {z // z ∈ ball (0 : ℂ) 1} := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  have htests := countableClusterTests_of_familyMeasurability h hγ hγ2 hα hμ hfam e'
  have hmeas : AEMeasurable H P := by
    have hm := aemeasurable_realDenseSequenceBallHorizon_of_tests (Measure.map μ P) (3 / 4)
      (fun ν i t => cluster ν 1 (e i) t) htests
    exact hm.comp_aemeasurable (h.aemeasurable_lqgMeasure hμ)
  refine ⟨H, hmeas, ?_⟩
  filter_upwards [ae_countableCentresHorizon_pos_of_upperBound h hγ hγ2 hα hμ h71 e,
    hcover, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ,
    h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ,
    h54 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hpos hcov hopen hmono hnull hlocal
  refine ⟨hpos, ?_⟩
  intro z hz
  have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num) hz
  have hop : ∀ i (t : Ioi (0 : ℝ)), IsOpen (cluster (μ ω) 1 (e i) t) := by
    intro i t
    exact (hopen t 1 t.property (by norm_num) (e i) (e' i).property).1
  have hmon : ∀ i, Monotone (fun t : Ioi (0 : ℝ) => cluster (μ ω) 1 (e i) t) := by
    intro i s t hst
    exact hmono s t 1 s.property hst (by norm_num) (e i) (e' i).property
  have hbefore : ∀ t ∈ Ioo (0 : ℝ) (H ω), closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
    intro t ht
    let t' : Ioi (0 : ℝ) := ⟨t, ht.1⟩
    have hc := closure_subset_closedBall_of_countable_centres
      (F := fun (j : {z // z ∈ ball (0 : ℂ) (1 / 2)}) t => cluster (μ ω) 1 j t)
      e hop hmon hcov (t := t') ht.2 ⟨z, hz⟩
    exact hc.trans (closedBall_subset_ball (by norm_num))
  obtain ⟨T, hT, _, hconditions, htouch⟩ := hlocal z hz
  refine ⟨regularizedClusterConditionsOn_of_horizon hT hpos
    (hopen T 1 hT (by norm_num) z hz1).1 hbefore htouch hconditions, ?_⟩
  intro t ht
  exact ⟨hbefore t ht, hnull z hz1 t ht.1 (hbefore t ht)⟩

end HarmonicBalls

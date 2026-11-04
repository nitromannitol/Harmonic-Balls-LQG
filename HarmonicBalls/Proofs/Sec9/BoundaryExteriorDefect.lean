import HarmonicBalls.Proofs.Sec9.BoundaryMassDefect

/-!
# Exterior boundary mass and weak uniqueness

The conservation identity bounds the mass of a subharmonic ball outside
the cluster closure by the cluster frontier mass outside the ball.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The exterior mass defect is bounded by the cluster frontier outside the
comparison ball. -/
theorem IsSubharmonicBall.exterior_mass_le_frontier_sdiff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t)) :
    μ (A \ closure (cluster μ R z t)) ≤ μ (frontier (cluster μ R z t) \ A) := by
  let C := cluster μ R z t
  obtain ⟨hsub, ν, hν, heq, _⟩ := hA.exists_boundary_measure_mass_defect
    hμ hR ht hz hV hcl hmass hopen
  have hinner : ν (frontier C ∩ A) ≤ μ ((A \ C) ∩ closure C) := by
    apply (hν _).trans
    apply measure_mono
    rintro x ⟨hx, hxA⟩
    refine ⟨⟨hxA, ?_⟩, frontier_subset_closure hx⟩
    rw [hopen.frontier_eq] at hx
    exact hx.2
  have hset : (A \ C) \ closure C = A \ closure C := by
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨⟨hxA, _⟩, hxcl⟩
      exact ⟨hxA, hxcl⟩
    · rintro ⟨hxA, hxcl⟩
      exact ⟨⟨hxA, fun hx => hxcl (subset_closure hx)⟩, hxcl⟩
  have hsplitμ := measure_sdiff_add_inter (μ := μ) (t := closure C)
    (A \ C) isClosed_closure.measurableSet
  rw [hset, heq] at hsplitμ
  have hsplitν := measure_sdiff_add_inter (μ := ν) (frontier C) hA.1.measurableSet
  have hfin : μ ((A \ C) ∩ closure C) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hmass]; exact ENNReal.ofReal_ne_top)
      (measure_mono (inter_subset_left.trans sdiff_subset))
  apply (add_le_add_iff_left_of_ne_top hfin).mp
  rw [hsplitμ, ← hsplitν]
  exact add_le_add (hν _) hinner

/-- It suffices for the cluster frontier outside the comparison ball to be
null to obtain the inclusion into the regularized cluster. -/
theorem IsSubharmonicBall.subset_regularizedCluster_of_null_exterior_frontier
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] (hμ : IsLocallyFiniteMeasure μ)
    {A : Set ℂ} {z : ℂ} (hA : IsSubharmonicBall μ A z)
    {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t))
    (hnull : μ (frontier (cluster μ R z t) \ A) = 0) :
    A ⊆ regularizedCluster μ R z t := by
  have hzero : μ (A \ closure (cluster μ R z t)) = 0 :=
    le_antisymm ((hA.exterior_mass_le_frontier_sdiff hμ hR ht hz hV hcl hmass hopen).trans_eq hnull) bot_le
  have hopen' : IsOpen (A \ closure (cluster μ R z t)) := hA.1.sdiff isClosed_closure
  have hsub : A ⊆ closure (cluster μ R z t) :=
    sdiff_eq_empty.mp ((hopen'.measure_eq_zero_iff μ).mp hzero)
  exact hA.1.subset_interior_iff.mpr hsub

/-- If an open set contains the cluster, its exterior cluster frontier is
exactly the common frontier of the two sets. -/
theorem frontier_sdiff_eq_inter_frontier_of_subset {C A : Set ℂ}
    (hA : IsOpen A) (hsub : C ⊆ A) :
    frontier C \ A = frontier C ∩ frontier A := by
  ext x
  constructor
  · rintro ⟨hx, hxA⟩
    exact ⟨hx, by rw [hA.frontier_eq]; exact ⟨closure_mono hsub (frontier_subset_closure hx), hxA⟩⟩
  · rintro ⟨hx, hxA⟩
    rw [hA.frontier_eq] at hxA
    exact ⟨hx, hxA.2⟩

/-- On one volume-growth event, weak uniqueness holds whenever the two
frontiers have null intersection. -/
theorem ae_subharmonicBall_uniqueness_of_null_common_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      μ ω (frontier (cluster (μ ω) R z t) ∩ frontier A) = 0 →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hV hopen hfull
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro A z t R ht hR hz hcl hA hmass hnull
  have hsub := hA.cluster_subset_of_volumeGrowth hV.1 hR ht (hV.2 R hR) hcl hmass
  have hnull' : μ ω (frontier (cluster (μ ω) R z t) \ A) = 0 := by
    rwa [frontier_sdiff_eq_inter_frontier_of_subset hA.1 hsub]
  have hreg := hA.subset_regularizedCluster_of_null_exterior_frontier hV.1 hR ht hz
    (hV.2 R hR) hcl hmass (hopen t R ht hR z hz).1 hnull'
  refine ⟨hsub, hreg, ?_⟩
  intro hregular
  apply Subset.antisymm ?_ hreg
  change interior (closure (cluster (μ ω) R z t)) ⊆ A
  rw [← hregular]
  exact interior_mono (closure_mono hsub)

end HarmonicBalls

import HarmonicBalls.Proofs.Sec9.SubharmonicSupersolution
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-!
# Boundary mass and weak uniqueness

The conservation identity assigns any missing cluster mass to a measure
dominated by the Liouville measure on the cluster frontier. Thus the mass
of a subharmonic ball outside the regularized cluster is bounded by that
frontier mass, without assuming the frontier is null.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- For a subharmonic ball of mass `t`, the mass outside the cluster equals
the boundary term in the obstacle conservation identity. -/
theorem IsSubharmonicBall.exists_boundary_measure_mass_defect
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t)) :
    cluster μ R z t ⊆ A ∧ ∃ ν : Measure ℂ, ν ≤ μ ∧
      μ (A \ cluster μ R z t) = ν (frontier (cluster μ R z t)) ∧
      μ (A \ regularizedCluster μ R z t) ≤ ν (frontier (cluster μ R z t)) := by
  have hsub := hA.cluster_subset_of_volumeGrowth hμ hR ht hV hcl hmass
  have hclustercl : closure (cluster μ R z t) ⊆ ball 0 R := (closure_mono hsub).trans hcl
  obtain ⟨_, _, hshift, _⟩ :=
    obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz t ht
  obtain ⟨hle, _, ν, hν, _, hidentity⟩ :=
    obstacleConservationOfMassGeneral_holds μ hμ R βm βp hR hV z hz t ht
  rw [← hshift] at hle hidentity
  have hfin : μ (cluster μ R z t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hsum : μ (cluster μ R z t) + μ (A \ cluster μ R z t) = μ A := by
    simpa only [union_eq_self_of_subset_left hsub] using
      (measure_add_sdiff (μ := μ) hopen.measurableSet.nullMeasurableSet A)
  have heq : μ (A \ cluster μ R z t) = ν (frontier (cluster μ R z t)) := by
    have h := congrArg (fun a : ℝ≥0∞ => a - μ (cluster μ R z t))
      (hsum.trans (hmass.trans (hidentity hclustercl).symm))
    simpa only [ENNReal.add_sub_cancel_left hfin] using h
  refine ⟨hsub, ν, hν, heq, ?_⟩
  rw [← heq]
  apply measure_mono
  exact sdiff_subset_sdiff_right (hopen.subset_interior_iff.mpr subset_closure)

/-- If the comparison set has null frontier, the conservation identity and
full support force it into the regularization of the cluster. -/
theorem IsSubharmonicBall.subset_regularizedCluster_of_null_frontier
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] (hμ : IsLocallyFiniteMeasure μ)
    {A : Set ℂ} {z : ℂ} (hA : IsSubharmonicBall μ A z)
    {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t)) (hnull : μ (frontier A) = 0) :
    A ⊆ regularizedCluster μ R z t := by
  let C := cluster μ R z t
  obtain ⟨hsub, ν, hν, heq, _⟩ := hA.exists_boundary_measure_mass_defect
    hμ hR ht hz hV hcl hmass hopen
  have houtside : frontier C \ A ⊆ frontier A := by
    intro x hx
    rw [hA.1.frontier_eq]
    exact ⟨closure_mono hsub (frontier_subset_closure hx.1), hx.2⟩
  have hνnull : ν (frontier A) = 0 := le_antisymm ((hν _).trans_eq hnull) bot_le
  have hzero : ν (frontier C \ A) = 0 := measure_mono_null houtside hνnull
  have hνbound : ν (frontier C) ≤ μ ((A \ C) ∩ closure C) := by
    have hsplit := measure_sdiff_add_inter (μ := ν) (frontier C) hA.1.measurableSet
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
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
      exact ⟨⟨hxA, fun hx => hxcl (by exact subset_closure hx)⟩, hxcl⟩
  have hsplit := measure_sdiff_add_inter (μ := μ) (t := closure C)
    (A \ C) isClosed_closure.measurableSet
  rw [hset, heq] at hsplit
  have hfin : μ ((A \ C) ∩ closure C) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hmass]; exact ENNReal.ofReal_ne_top)
      (measure_mono (inter_subset_left.trans sdiff_subset))
  have hle : μ (A \ closure C) + μ ((A \ C) ∩ closure C) ≤
      0 + μ ((A \ C) ∩ closure C) := by
    rw [zero_add, hsplit]
    exact hνbound
  have hzero' : μ (A \ closure C) = 0 := by
    exact le_antisymm ((add_le_add_iff_left_of_ne_top hfin).mp hle) bot_le
  have hopen' : IsOpen (A \ closure C) := hA.1.sdiff isClosed_closure
  have hsubcl : A ⊆ closure C := sdiff_eq_empty.mp ((hopen'.measure_eq_zero_iff μ).mp hzero')
  exact hA.1.subset_interior_iff.mpr hsubcl

/-- Simultaneously for all subharmonic balls compactly contained in their
disc, the weak uniqueness defect is at most the cluster frontier mass. -/
theorem ae_subharmonicBall_weak_defect_le_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧
      μ ω (A \ regularizedCluster (μ ω) R z t) ≤
        μ ω (frontier (cluster (μ ω) R z t)) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV hopen
  intro A z t R ht hR hz hcl hA hmass
  obtain ⟨hsub, ν, hν, _, hdefect⟩ := hA.exists_boundary_measure_mass_defect
    hV.1 hR ht hz (hV.2 R hR) hcl hmass (hopen t R ht hR z hz).1
  exact ⟨hsub, hdefect.trans (hν _)⟩

/-- A null frontier of the subharmonic ball itself gives both inclusions
through the regularized cluster. If the ball is regular open, it equals the
regularized cluster. -/
theorem ae_subharmonicBall_uniqueness_of_own_null_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      μ ω (frontier A) = 0 →
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
  have hreg := hA.subset_regularizedCluster_of_null_frontier hV.1 hR ht hz
    (hV.2 R hR) hcl hmass (hopen t R ht hR z hz).1 hnull
  refine ⟨hsub, hreg, ?_⟩
  intro hregular
  apply Subset.antisymm ?_ hreg
  change interior (closure (cluster (μ ω) R z t)) ⊆ A
  rw [← hregular]
  exact interior_mono (closure_mono hsub)

end HarmonicBalls

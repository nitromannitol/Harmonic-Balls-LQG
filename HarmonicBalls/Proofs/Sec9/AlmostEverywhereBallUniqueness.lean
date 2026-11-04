import HarmonicBalls.Proofs.Sec9.VolumeGrowthUniqueness
import HarmonicBalls.Proofs.Sec9.UnitDiscWeakUniqueness

/-! # Almost-everywhere uniqueness of subharmonic balls

A null cluster frontier turns the inclusion of the cluster in a comparison
ball and the common-closure sandwich into almost-everywhere equality.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- If two open sets contain the same open set and lie in its closure, their
symmetric difference and their frontiers are contained in its frontier. -/
theorem frontier_and_sdiff_subset_of_common_closure
    {X : Type*} [TopologicalSpace X] {C A B : Set X}
    (hC : IsOpen C) (hA : IsOpen A) (hB : IsOpen B)
    (hCA : C ⊆ A) (hAC : A ⊆ closure C)
    (hCB : C ⊆ B) (hBC : B ⊆ closure C) :
    frontier A ⊆ frontier C ∧ frontier B ⊆ frontier C ∧
      A \ B ⊆ frontier C ∧ B \ A ⊆ frontier C := by
  have hfront (D : Set X) (hD : IsOpen D) (hCD : C ⊆ D) (hDC : D ⊆ closure C) :
      frontier D ⊆ frontier C := by
    rw [hD.frontier_eq, hC.frontier_eq]
    intro x hx
    exact ⟨closure_minimal hDC isClosed_closure hx.1, fun hxC => hx.2 (hCD hxC)⟩
  have hdiff (D E : Set X) (hDC : D ⊆ closure C) (hCE : C ⊆ E) :
      D \ E ⊆ frontier C := by
    rw [hC.frontier_eq]
    intro x hx
    exact ⟨hDC hx.1, fun hxC => hx.2 (hCE hxC)⟩
  exact ⟨hfront A hA hCA hAC, hfront B hB hCB hBC,
    hdiff A B hAC hCB, hdiff B A hBC hCA⟩

/-- Almost surely, two equal-mass subharmonic balls compactly contained in
the unit disc agree almost everywhere and each has zero boundary measure.
The ambient radius is arbitrary; no regular-open assumption is needed. -/
theorem ae_subharmonicBall_null_frontier_and_ae_eq_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure B ⊆ ball 0 R →
      closure A ⊆ ball 0 1 → closure B ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω A = ENNReal.ofReal t → μ ω B = ENNReal.ofReal t →
      μ ω (frontier A) = 0 ∧ μ ω (frontier B) = 0 ∧
        μ ω (A \ B) = 0 ∧ μ ω (B \ A) = 0 ∧
        (μ ω).restrict A = (μ ω).restrict B := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  let h8 := boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2
      (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2)) h82
  filter_upwards [ae_subharmonicBall_sandwich_inside_unit_disc_of_volumeGrowth hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_boundary_null_of_unit_disc hI2 h8 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
      with ω hcompare hnull hopen
  intro A B z t R ht hR hz hAcl hBcl hAcl1 hBcl1 hA hB hAm hBm
  obtain ⟨hCA, hAC, _⟩ := hcompare A z t R ht hR hz hAcl hAcl1 hA hAm
  obtain ⟨hCB, hBC, _⟩ := hcompare B z t R ht hR hz hBcl hBcl1 hB hBm
  have hCclR : closure (cluster (μ ω) R z t) ⊆ ball 0 R := (closure_mono hCA).trans hAcl
  have hCcl1 : closure (cluster (μ ω) R z t) ⊆ ball 0 1 := (closure_mono hCA).trans hAcl1
  have hzC := hnull R t hR ht z hz hCclR hCcl1
  have hsets := frontier_and_sdiff_subset_of_common_closure (hopen t R ht hR z hz).1
    hA.1 hB.1 hCA (hAC.trans interior_subset) hCB (hBC.trans interior_subset)
  have hAB := measure_mono_null hsets.2.2.1 hzC
  have hBA := measure_mono_null hsets.2.2.2 hzC
  exact ⟨measure_mono_null hsets.1 hzC, measure_mono_null hsets.2.1 hzC, hAB, hBA,
    Measure.restrict_congr_set (ae_eq_set.mpr ⟨hAB, hBA⟩)⟩

/-- The same conclusion for equal-mass subharmonic balls, stated without
choosing a mass parameter or ambient radius. -/
theorem ae_subharmonicBall_restrict_eq_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ),
      closure A ⊆ ball 0 1 → closure B ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω A = μ ω B →
      μ ω (frontier A) = 0 ∧ μ ω (frontier B) = 0 ∧
        (μ ω).restrict A = (μ ω).restrict B := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_null_frontier_and_ae_eq_inside_unit_disc
    hI2 h82 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro A B z hAcl hBcl hA hB hmass
  let t : ℝ := (μ ω A).toReal
  have hfinite : μ ω A ≠ ⊤ := ne_of_lt hA.2.2.2.1
  have ht : 0 < t := ENNReal.toReal_pos hA.2.2.1.ne' hfinite
  have hmassA : μ ω A = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfinite).symm
  have hmassB : μ ω B = ENNReal.ofReal t := hmass.symm.trans hmassA
  have hz : z ∈ ball (0 : ℂ) 1 := hAcl (subset_closure hA.2.1)
  obtain ⟨hfa, hfb, _, _, hres⟩ := hω A B z t 1 ht zero_lt_one hz
    hAcl hBcl hAcl hBcl hA hB hmassA hmassB
  exact ⟨hfa, hfb, hres⟩

end HarmonicBalls

import HarmonicBalls.Proofs.Sec5.ObstacleCentreContinuity
import HarmonicBalls.Proofs.Sec5.DenseVolumeGrowth
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Stability in measure under motion of the pole

Lower stability of the cluster in its pole implies that its lost mass tends
to zero. At a mass-saturating cluster, an upper bound on nearby cluster mass
also controls the newly gained mass.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

/-- Pointwise eventual inclusion and finite mass imply convergence of the
lost mass to zero. -/
theorem tendsto_measure_sdiff_zero_of_eventually_mem
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : Set α) (B : ℕ → Set α) (hA : MeasurableSet A)
    (hB : ∀ n, MeasurableSet (B n)) (hfin : μ A ≠ ⊤)
    (hmem : ∀ x ∈ A, ∀ᶠ n in atTop, x ∈ B n) :
    Tendsto (fun n => μ (A \ B n)) atTop (𝓝 0) := by
  have h := tendsto_measure_of_tendsto_indicator (μ := μ) (A := ∅)
    (As := fun n : ℕ => A \ B n) atTop (fun n => hA.diff (hB n))
    hA hfin (Eventually.of_forall fun _ => sdiff_subset)
  simp only [measure_empty] at h
  apply h
  intro x
  by_cases hx : x ∈ A
  · filter_upwards [hmem x hx] with n hn
    simp [hn]
  · exact Eventually.of_forall fun n => by simp [hx]

/-- If a moving set has at most the mass of the limiting set, then its gained
mass is no greater than the lost mass. -/
theorem measure_sdiff_le_of_measure_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {A B : Set α} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hfin : μ A ≠ ⊤) (hmass : μ B ≤ μ A) :
    μ (B \ A) ≤ μ (A \ B) := by
  have hi : μ (A ∩ B) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  have hadd : μ (A ∩ B) + μ (B \ A) ≤ μ (A ∩ B) + μ (A \ B) := by
    rw [inter_comm A B, measure_inter_add_sdiff B hA,
      inter_comm B A, measure_inter_add_sdiff A hB]
    exact hmass
  exact ENNReal.le_of_add_le_add_left hi hadd

/-- Cluster mass cannot be lost abruptly when its pole moves. -/
theorem tendsto_measure_cluster_sdiff_of_centre
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {t : ℝ} (ht : 0 < t) (z : ball (0 : ℂ) R)
    (zs : ℕ → ball (0 : ℂ) R) (hzs : Tendsto zs atTop (𝓝 z)) :
    Tendsto (fun n => μ (cluster μ R z t \ cluster μ R (zs n) t)) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure μ := hμ
  have hopen (w : ball (0 : ℂ) R) : IsOpen (cluster μ R w t) :=
    (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hR hV w.property ht).1
  have hfinite : μ (cluster μ R z t) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsCompact.measure_lt_top (μ := μ) (isCompact_closedBall (0 : ℂ) R)).ne
      (measure_mono (cluster_subset_ball.trans ball_subset_closedBall))
  apply tendsto_measure_sdiff_zero_of_eventually_mem μ _ _ (hopen z).measurableSet
    (fun n => (hopen (zs n)).measurableSet) hfinite
  intro x hx
  exact hzs.eventually ((isOpen_cluster_centre_section hμ hR hV ht x).mem_nhds hx)

/-- At a mass-saturating cluster, upper mass bounds turn lower stability into
continuity in symmetric-difference measure. -/
theorem tendsto_measure_cluster_symmDiff_of_centre
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {t : ℝ} (ht : 0 < t) (z : ball (0 : ℂ) R)
    (zs : ℕ → ball (0 : ℂ) R) (hzs : Tendsto zs atTop (𝓝 z))
    (hmass : ∀ n, μ (cluster μ R (zs n) t) ≤ μ (cluster μ R z t)) :
    Tendsto (fun n => μ (cluster μ R z t ∆ cluster μ R (zs n) t)) atTop (𝓝 0) := by
  let : IsLocallyFiniteMeasure μ := hμ
  have hopen (w : ball (0 : ℂ) R) : IsOpen (cluster μ R w t) :=
    (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hR hV w.property ht).1
  have hfinite : μ (cluster μ R z t) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsCompact.measure_lt_top (μ := μ) (isCompact_closedBall (0 : ℂ) R)).ne
      (measure_mono (cluster_subset_ball.trans ball_subset_closedBall))
  have hlost := tendsto_measure_cluster_sdiff_of_centre hμ hR hV ht z zs hzs
  have hgained : Tendsto (fun n => μ (cluster μ R (zs n) t \ cluster μ R z t))
      atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlost
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n =>
        measure_sdiff_le_of_measure_le μ (hopen z).measurableSet
          (hopen (zs n)).measurableSet hfinite (hmass n))
  have hsum := hlost.add hgained
  simpa only [zero_add, measure_symmDiff_eq (hopen z).measurableSet.nullMeasurableSet
    (hopen (zs _)).measurableSet.nullMeasurableSet] using hsum

universe u

/-- Almost surely, every compactly contained cluster varies continuously in
measure as its pole moves. The event is simultaneous in radius, time, pole,
and convergent sequences of poles. -/
theorem ae_compact_cluster_measure_continuous_in_centre
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ z : ball (0 : ℂ) R,
      closure (cluster (μ ω) R z t) ⊆ ball 0 R →
      ∀ zs : ℕ → ball (0 : ℂ) R, Tendsto zs atTop (𝓝 z) →
      Tendsto (fun n => (μ ω) (cluster (μ ω) R z t ∆
        cluster (μ ω) R (zs n) t)) atTop (𝓝 0) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hb := clusterBoundaryNullAllRadii_of_dyadic_typical_scales hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
  filter_upwards [hV, clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hb γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hv hm hbω
  intro R t hR ht z hcompact zs hzs
  have hzero := hbω R t hR ht z z.property hcompact
  have heq := (hm R t hR ht z z.property).2.2 hcompact hzero
  apply tendsto_measure_cluster_symmDiff_of_centre hv.1 hR (hv.2 R hR) ht z zs hzs
  intro n
  exact ((hm R t hR ht (zs n) (zs n).property).1).trans_eq heq.symm

/-- A positive-mass set outside a compactly contained cluster cannot be
covered by clusters with sufficiently nearby poles. This does not assert that
a complementary component persists. -/
theorem ae_positive_mass_outside_cluster_not_covered_near_centre
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ z : ball (0 : ℂ) R,
      closure (cluster (μ ω) R z t) ⊆ ball 0 R →
      ∀ (U : Set ℂ), U ⊆ (cluster (μ ω) R z t)ᶜ → μ ω U ≠ 0 →
      ∀ zs : ℕ → ball (0 : ℂ) R, Tendsto zs atTop (𝓝 z) →
      ∀ᶠ n in atTop, ¬ U ⊆ cluster (μ ω) R (zs n) t := by
  filter_upwards [ae_compact_cluster_measure_continuous_in_centre hI2 h82 hγ hγ2 hα
    P hC hcirc μ hGFF hμ] with ω hω
  intro R t hR ht z hcompact U hU hUpos zs hzs
  have hlim : Tendsto (fun n => (μ ω) (U ∩ cluster (μ ω) R (zs n) t)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hω R t hR ht z hcompact zs hzs)
    · exact Eventually.of_forall fun _ => bot_le
    · apply Eventually.of_forall
      intro n
      apply measure_mono
      intro x hx
      simp only [symmDiff_def]
      exact Or.inr ⟨hx.2, hU hx.1⟩
  have hnear := hlim.eventually (Iio_mem_nhds (pos_iff_ne_zero.mpr hUpos))
  filter_upwards [hnear] with n hn hsubset
  have heq : U ∩ cluster (μ ω) R (zs n) t = U := inter_eq_left.mpr hsubset
  rw [heq] at hn
  exact (lt_irrefl _ hn)

end HarmonicBalls

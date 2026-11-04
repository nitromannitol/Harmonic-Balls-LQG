import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation
import HarmonicBalls.Proofs.Sec6.GreenIntegrability
import HarmonicBalls.Proofs.Sec6.TruncatedOdometerLaplacian

/-! # The auxiliary potential in the annular odometer estimate

The source measure in Lemma 6.10 is dominated by the LQG measure away
from the pole. Its Green potential is therefore bounded by the annular
Green-potential supremum, including the diagonal convention of that supremum.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Laplacian
open scoped ENNReal

/-- A Green potential of a dominated measure is bounded by the annular
Green-potential supremum. -/
theorem restricted_greenPotential_le_annulusGreenPotentialSup
    {μ ν : Measure ℂ} {c x : ℂ} {a b : ℝ}
    (hν : ν ≤ μ) (hx : x ∈ annulus c a b)
    (hint : IntegrableOn (greenFunction (ball c b) x) (annulus c a b) ν) :
    ENNReal.ofReal (∫ y in annulus c a b, greenFunction (ball c b) x y ∂ν) ≤
      annulusGreenPotentialSup μ c a b := by
  have hnonneg : ∀ y, 0 ≤ greenFunction (ball c b) x y :=
    greenFunction_nonneg isBounded_ball x
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnonneg)]
  calc
    (∫⁻ y in annulus c a b, ENNReal.ofReal (greenFunction (ball c b) x y) ∂ν) ≤
        ∫⁻ y in annulus c a b,
          (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball c b) x y)) ∂ν := by
      apply lintegral_mono
      intro y
      change ENNReal.ofReal (greenFunction (ball c b) x y) ≤
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball c b) x y))
      split_ifs <;> simp
    _ ≤ ∫⁻ y in annulus c a b,
          (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball c b) x y)) ∂μ :=
      lintegral_mono_fn' (Measure.restrict_mono (Subset.rfl) hν) (fun _ => le_rfl)
    _ ≤ annulusGreenPotentialSup μ c a b := le_iSup_of_le x (le_iSup_of_le hx le_rfl)

/-- On a set inside the ambient domain, the cluster and frontier parts of
the odometer's Laplacian together are dominated by the original measure. -/
theorem cluster_frontier_measure_restrict_le
    {μ ν : Measure ℂ} {U A Λ : Set ℂ} (hΛ : IsOpen Λ)
    (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hν : ν.restrict U ≤ μ.restrict U) :
    (μ.restrict Λ + ν.restrict (frontier Λ)).restrict A ≤ μ.restrict A := by
  have hfront : frontier Λ ⊆ Λᶜ := by
    intro x hx hxΛ
    exact (disjoint_left.mp disjoint_interior_frontier) (by simpa [hΛ.interior_eq] using hxΛ) hx
  have hνA : ν.restrict A ≤ μ.restrict A := by
    have h := Measure.restrict_mono (subset_refl A) hν
    simpa only [Measure.restrict_restrict_of_subset hAU] using h
  have hsecond : (ν.restrict (frontier Λ)).restrict A ≤ (μ.restrict A).restrict Λᶜ := by
    rw [Measure.restrict_comm hA]
    exact (Measure.restrict_mono_set (ν.restrict A) hfront).trans
      (Measure.restrict_mono (subset_refl Λᶜ) hνA)
  have hfirst : (μ.restrict Λ).restrict A = (μ.restrict A).restrict Λ :=
    Measure.restrict_comm hA
  rw [Measure.restrict_add, hfirst]
  exact (add_le_add_right hsecond _).trans_eq (Measure.restrict_add_restrict_compl (μ := μ.restrict A) (s := Λ) hΛ.measurableSet)

/-- Away from the pole the distributional Laplacian of the odometer is a
positive measure dominated by the original measure. -/
theorem odometer_hasLaplacian_dominated_away_from_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {A : Set ℂ} (hA : MeasurableSet A) (hAsub : A ⊆ ball (0 : ℂ) R \ {z}) :
    ∃ η : Measure ℂ, η ≤ μ ∧ η.restrict A = η ∧
      HasLaplacian (odometer μ R z t) η 0 A := by
  obtain ⟨hopen, _, ν, _, _, hν, _, hΔ⟩ :=
    cluster_open_laplacian_of_general greenFunctionBall obstacleNonCoincidenceHarmonicGeneral_holds
      shiftedOdometerLaplacianGeneral_holds obstacleCompatibilityShiftStep_holds hμ hR hV hz ht
  let σ := μ.restrict (cluster μ R z t) + ν.restrict (frontier (cluster μ R z t))
  let η := σ.restrict A
  have hle : η ≤ μ := (cluster_frontier_measure_restrict_le hopen hA
    (fun x hx => (hAsub hx).1) hν).trans Measure.restrict_le_self
  refine ⟨η, hle, ?_, hΔ.1.mono_set (fun x hx => (hAsub hx).1), ?_⟩
  · simp [η, Measure.restrict_restrict hA]
  ·
    intro φ hφ
    have hφR : IsTestFunction (ball (0 : ℂ) R) φ :=
      ⟨hφ.1, hφ.2.1, hφ.2.2.trans (fun x hx => (hAsub hx).1)⟩
    obtain ⟨hi, _, heq⟩ := hΔ.2 φ hφR
    have hzero (x : ℂ) (hx : x ∉ A) : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ.2.2 hx'))
    have hzA : z ∉ A := fun hz' => (hAsub hz').2 rfl
    have hrest : ∫ x, φ x ∂η = ∫ x, φ x ∂σ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero x hx)
    refine ⟨hi.mono_measure Measure.restrict_le_self, integrable_zero_measure, ?_⟩
    rw [hrest, heq, integral_smul_measure, integral_dirac, hzero z hzA]
    simp [σ]

end HarmonicBalls.Section6

import HarmonicBalls.Proofs.Sec6.AnnulusOdometerPotential
import HarmonicBalls.Proofs.Sec6.DominatedDiscPotential

/-! # Harmonic correction of the odometer on an annulus

The restricted Laplacian measure yields the auxiliary Green potential in
Lemma 6.10. Its sum with the odometer has zero distributional Laplacian.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Laplacian
open scoped ENNReal

/-- The odometer on an annulus away from its pole has a nonnegative Green
correction, controlled by the annular Green-potential supremum, whose sum
with the odometer has zero distributional Laplacian. -/
theorem exists_annulus_odometer_harmonic_correction
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) R \ {z}) :
    ∃ q : ℂ → ℝ,
      ContinuousOn q (annulus c a b) ∧
      (∀ x, 0 ≤ q x) ∧
      (∀ x ∈ annulus c a b, ENNReal.ofReal (q x) ≤ annulusGreenPotentialSup μ c a b) ∧
      (∀ x ∈ annulus c a b, 0 ≤ odometer μ R z t x + q x) ∧
      HasLaplacian (fun x => odometer μ R z t x + q x) 0 0 (annulus c a b) ∧
      IsSuperharmonicOn (annulus c a b) (fun x => odometer μ R z t x + q x) ∧
      IsSuperharmonicOn (annulus c a b) (fun x => -(odometer μ R z t x + q x)) := by
  let A := annulus c a b
  have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAball : A ⊆ ball (0 : ℂ) R := fun x hx => (hA hx).1
  have hball : ball c b ⊆ ball (0 : ℂ) R :=
    ball_subset_ball_of_annulus_subset_ball hab hAball
  obtain ⟨η, hη, hηA, hΔv⟩ := odometer_hasLaplacian_dominated_away_from_pole
    hμ hR hV hz ht hAopen.measurableSet hA
  let q : ℂ → ℝ := fun x => ∫ y in A, greenFunction (ball c b) x y ∂η
  obtain ⟨hqc, hΔq⟩ := dominated_restricted_greenPotential_center_regular
    hμ hη hb hV hball (A := A) sdiff_subset
  have hp : HasLaplacian q 0 (η.restrict A) (ball c b) := hΔq
  have hΔqA : HasLaplacian q 0 η A := by
    refine ⟨hp.1.mono_set sdiff_subset, fun φ hφ => ?_⟩
    simpa only [hηA] using hp.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans sdiff_subset⟩
  have hnonneg : ∀ x, 0 ≤ q x := fun x =>
    integral_nonneg (greenFunction_nonneg isBounded_ball x)
  have hbound : ∀ x ∈ A, ENNReal.ofReal (q x) ≤ annulusGreenPotentialSup μ c a b := by
    intro x hx
    let : IsLocallyFiniteMeasure μ := hμ
    have hint := integrable_greenFunction_of_volumeGrowth hR isOpen_ball hball hV
      (ball_subset_closedBall (hAball hx))
    exact restricted_greenPotential_le_annulusGreenPotentialSup hη hx
      (hint.mono_measure (Measure.restrict_le_self.trans hη))
  have hΔsum : HasLaplacian (fun x => odometer μ R z t x + q x) 0 0 A := by
    refine ⟨hΔv.1.add hΔqA.1, fun φ hφ => ⟨integrable_zero_measure, integrable_zero_measure, ?_⟩⟩
    obtain ⟨_, _, ev⟩ := hΔv.2 φ hφ
    obtain ⟨_, _, eq⟩ := hΔqA.2 φ hφ
    have hfun : (fun x => (odometer μ R z t x + q x) * Δ φ x) =
        fun x => odometer μ R z t x * Δ φ x + q x * Δ φ x := by
      funext x
      ring
    rw [hfun, integral_add (integrable_mul_laplacian hΔv.1 hφ)
      (integrable_mul_laplacian hΔqA.1 hφ), ev, eq]
    simp
  have hcont : ContinuousOn (fun x => odometer μ R z t x + q x) A :=
    ((odometer_continuousOn_and_subharmonic hμ hR hV hz ht).1.mono hA).add
      (hqc.mono (sdiff_subset.trans ball_subset_closedBall))
  have hLEneg : LaplacianLE (fun x => -(odometer μ R z t x + q x)) 0 A := by
    refine ⟨hΔsum.1.neg, fun φ hφ _ _ => ?_⟩
    have hfun : (fun x => -(odometer μ R z t x + q x) * Δ φ x) =
        fun x => -((odometer μ R z t x + q x) * Δ φ x) := by
      funext x
      ring
    rw [hfun, integral_neg, (hΔsum.2 φ hφ).2.2]
    simp
  have hsum0 : ∀ x ∈ A, 0 ≤ odometer μ R z t x + q x := by
    intro x hx
    exact add_nonneg (odometer_nonneg ht.le (ball_subset_closedBall (hA hx).1) (hA hx).2)
      (hnonneg x)
  exact ⟨q, hqc.mono (sdiff_subset.trans ball_subset_closedBall), hnonneg, hbound, hsum0, hΔsum,
    superharmonicOfLaplacianLEStep_holds A _ hAopen hcont hΔsum.laplacianLE,
    superharmonicOfLaplacianLEStep_holds A _ hAopen hcont.neg hLEneg⟩

end HarmonicBalls.Section6

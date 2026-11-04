import HarmonicBalls.Proofs.Sec10.DominatedComponentRiesz
import HarmonicBalls.Proofs.Sec6.ContinuousHarmonic

/-! # Harmonic correction for pole-avoiding component unions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6 InnerProductSpace
open scoped ENNReal

/-- The truncated odometer of a union of local components omitting the pole
has a nonnegative harmonic Green correction on the whole annulus, even when
the annulus contains the pole. -/
theorem exists_pole_avoiding_annulus_harmonic_correction
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) R)
    {Λ : Set ℂ} (hΛsub : Λ ⊆ annulus c a b ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (annulus c a b ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) :
    ∃ q : ℂ → ℝ,
      ContinuousOn q (annulus c a b) ∧
      (∀ x, 0 ≤ q x) ∧
      (∀ x ∈ annulus c a b, ENNReal.ofReal (q x) ≤ annulusGreenPotentialSup μ c a b) ∧
      (∀ x ∈ annulus c a b, 0 ≤ Λ.indicator (odometer μ R z t) x + q x) ∧
      HasLaplacian (fun x => Λ.indicator (odometer μ R z t) x + q x) 0 0
        (annulus c a b) ∧
      IsSuperharmonicOn (annulus c a b)
        (fun x => Λ.indicator (odometer μ R z t) x + q x) ∧
      IsSuperharmonicOn (annulus c a b)
        (fun x => -(Λ.indicator (odometer μ R z t) x + q x)) := by
  classical
  let A := annulus c a b
  have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hball : ball c b ⊆ ball (0 : ℂ) R :=
    ball_subset_ball_of_annulus_subset_ball hab hA
  obtain ⟨η, hη, hηA, hΔv⟩ := odometer_indicator_union_components_hasLaplacian_dominated
    hμ hR hV hz ht hAopen hA hΛsub hcomp hzΛ
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
      (ball_subset_closedBall (hA hx))
    exact restricted_greenPotential_le_annulusGreenPotentialSup hη hx
      (hint.mono_measure (Measure.restrict_le_self.trans hη))
  have hΔsum : HasLaplacian (fun x => Λ.indicator (odometer μ R z t) x + q x) 0 0 A := by
    refine ⟨hΔv.1.add hΔqA.1, fun φ hφ => ⟨integrable_zero_measure, integrable_zero_measure, ?_⟩⟩
    obtain ⟨_, _, ev⟩ := hΔv.2 φ hφ
    obtain ⟨_, _, eq⟩ := hΔqA.2 φ hφ
    have hfun : (fun x => (Λ.indicator (odometer μ R z t) x + q x) * Δ φ x) =
        fun x => Λ.indicator (odometer μ R z t) x * Δ φ x + q x * Δ φ x := by
      funext x
      ring
    rw [hfun, integral_add (integrable_mul_laplacian hΔv.1 hφ)
      (integrable_mul_laplacian hΔqA.1 hφ), ev, eq]
    simp
  have hcont : ContinuousOn (fun x => Λ.indicator (odometer μ R z t) x + q x) A :=
    (odometer_indicator_union_components_continuousOn_and_subharmonic_of_pole_not_mem
      hμ hR hV hz ht hAopen hA hΛsub hcomp hzΛ).1.add
      (hqc.mono (sdiff_subset.trans ball_subset_closedBall))
  have hLEneg : LaplacianLE (fun x => -(Λ.indicator (odometer μ R z t) x + q x)) 0 A := by
    refine ⟨hΔsum.1.neg, fun φ hφ _ _ => ?_⟩
    have hfun : (fun x => -(Λ.indicator (odometer μ R z t) x + q x) * Δ φ x) =
        fun x => -((Λ.indicator (odometer μ R z t) x + q x) * Δ φ x) := by
      funext x
      ring
    rw [hfun, integral_neg, (hΔsum.2 φ hφ).2.2]
    simp
  have hsum0 : ∀ x ∈ A, 0 ≤ Λ.indicator (odometer μ R z t) x + q x := by
    intro x hx
    apply add_nonneg _ (hnonneg x)
    by_cases hxΛ : x ∈ Λ
    · have hxz : x ≠ z := by intro h; subst x; exact hzΛ hxΛ
      simpa only [indicator_of_mem hxΛ] using
        odometer_nonneg ht.le (ball_subset_closedBall (hA hx)) (by simpa using hxz)
    · simp [hxΛ]
  exact ⟨q, hqc.mono (sdiff_subset.trans ball_subset_closedBall), hnonneg, hbound, hsum0, hΔsum,
    superharmonicOfLaplacianLEStep_holds A _ hAopen hcont hΔsum.laplacianLE,
    superharmonicOfLaplacianLEStep_holds A _ hAopen hcont.neg hLEneg⟩

/-- The Green-corrected truncation is classically harmonic and nonnegative on
an annulus even if the annulus contains the pole. -/
theorem exists_pole_avoiding_annulus_classical_harmonic_correction
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) R)
    {Λ : Set ℂ} (hΛsub : Λ ⊆ annulus c a b ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (annulus c a b ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) :
    ∃ q : ℂ → ℝ,
      ContinuousOn q (annulus c a b) ∧ (∀ x, 0 ≤ q x) ∧
      (∀ x ∈ annulus c a b, ENNReal.ofReal (q x) ≤ annulusGreenPotentialSup μ c a b) ∧
      (∀ x ∈ annulus c a b, 0 ≤ Λ.indicator (odometer μ R z t) x + q x) ∧
      HarmonicOnNhd (fun x => Λ.indicator (odometer μ R z t) x + q x) (annulus c a b) := by
  obtain ⟨q, hqc, hq0, hbound, hsum0, _, hsup, hinf⟩ :=
    exists_pole_avoiding_annulus_harmonic_correction hμ hR hV hz ht hab hb hA hΛsub hcomp hzΛ
  have hAopen : IsOpen (annulus c a b) := isOpen_ball.sdiff isClosed_closedBall
  have hcont : ContinuousOn (fun x => Λ.indicator (odometer μ R z t) x + q x) (annulus c a b) :=
    (odometer_indicator_union_components_continuousOn_and_subharmonic_of_pole_not_mem
      hμ hR hV hz ht hAopen hA hΛsub hcomp hzΛ).1.add hqc
  exact ⟨q, hqc, hq0, hbound, hsum0,
    harmonicOnNhd_of_superharmonic_and_neg hAopen hcont hsup hinf⟩

end HarmonicBalls

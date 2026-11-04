import HarmonicBalls.Steps.Sec11.PinchAuxiliaryThresholds
import HarmonicBalls.Proofs.Sec6.GreenPotentialBound
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Steps.Sec3.Basic

/-! # Finiteness of annular Green potentials under volume growth -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Volume growth controls the singularity of the Green kernel uniformly on
an annulus, including the extended kernel's infinite diagonal value. -/
theorem annulusGreenPotentialSup_ne_top_of_volumeGrowth
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {a b βminus βplus : ℝ}
    (hb : 0 < b) (hV : VolumeGrowth μ b βminus βplus) :
    annulusGreenPotentialSup μ 0 a b ≠ ∞ := by
  obtain ⟨M, hM⟩ := Section6.greenPotential_bddAbove_of_volumeGrowth hb
    isOpen_ball (Set.Subset.rfl : ball (0 : ℂ) b ⊆ ball 0 b) hV
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  unfold annulusGreenPotentialSup
  refine iSup_le fun x => iSup_le fun hx => ?_
  have hxball : x ∈ ball (0 : ℂ) b := hx.1
  have hμx : μ {x} = 0 := hV.measure_singleton hxball
  have hae : ∀ᵐ y ∂μ, y ≠ x := ae_iff.mpr (by simpa using hμx)
  have hI := Section6.integrable_greenFunction_of_volumeGrowth hb isOpen_ball
    (Set.Subset.rfl : ball (0 : ℂ) b ⊆ ball 0 b) hV (ball_subset_closedBall hxball)
  have hnonneg : ∀ y, 0 ≤ greenFunction (ball (0 : ℂ) b) x y :=
    greenFunction_nonneg isBounded_ball x
  have heq : (∫⁻ y in annulus (0 : ℂ) a b,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball 0 b) x y)) ∂μ) =
      ∫⁻ y in annulus (0 : ℂ) a b, ENNReal.ofReal (greenFunction (ball 0 b) x y) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hae] with y hy
    simp [hy]
  rw [heq]
  calc
    (∫⁻ y in annulus (0 : ℂ) a b, ENNReal.ofReal (greenFunction (ball 0 b) x y) ∂μ) ≤
        ∫⁻ y, ENNReal.ofReal (greenFunction (ball 0 b) x y) ∂μ := by
          exact lintegral_mono' (Measure.restrict_le_self) (fun _ => le_rfl)
    _ = ENNReal.ofReal (greenPotential (ball 0 b) μ x) := by
      rw [greenPotential, ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hnonneg)]
    _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (hM x)

universe u

/-- The annular Green-potential supremum of the singular-field LQG measure is
almost surely finite, conditional on the volume-growth statement. -/
theorem ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 a b ≠ ∞ := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ₂ hα hgff hμ
  filter_upwards [hV] with ω hω
  let : IsLocallyFiniteMeasure (μ ω) := hω.1
  exact annulusGreenPotentialSup_ne_top_of_volumeGrowth hb (hω.2 b hb)

/-- On a positive-mass event, LQG volume growth supplies the finite Green
threshold while the Euclidean length-metric property supplies the strict
sphere-distance threshold. -/
theorem exists_positive_measure_pinch_auxiliary_thresholds_of_lqgVolumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (A : Set Ω) (D : Ω → ℂ → ℂ → ℝ) {δ M : ℝ} (hδ : 0 < δ)
    (hA : 0 < P A) (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ n m : ℕ, 0 < n ∧ 0 < P {ω | ω ∈ A ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))) ∧
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 < (m : ℝ≥0∞)} := by
  exact exists_positive_measure_pinch_auxiliary_thresholds P A D μ hδ hA hmetric
    (ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth hgrowth hγ hγ₂ hα hgff hμ 3 (by norm_num))

end HarmonicBalls

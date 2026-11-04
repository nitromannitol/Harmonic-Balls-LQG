import HarmonicBalls.Proofs.Sec6.DiscPotentialComparison
import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation
import HarmonicBalls.Proofs.Sec6.GreenIntegrability

/-! # Disc mass and truncated odometers

The restricted Green-potential regularity supplies the analytic hypotheses
in the disc mass comparison from the proof of Lemma 6.8.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Laplacian
open scoped ENNReal

/-- A disc carrying a fixed fraction of the mass has a boundary point at
which the truncated odometer controls that mass. -/
theorem mass_le_truncated_odometer_of_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U Λ A : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hΛsub : Λ ⊆ U ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (U ∩ cluster μ R z t) x ⊆ Λ)
    {c : ℂ} {d : ℝ} {N : ℕ} (hd : 0 < d) (hdisc : closedBall c (2 * d) ⊆ U)
    (hmass : μ (A ∩ Λ) ≤ (N : ℝ≥0∞) * μ (ball c d ∩ Λ)) :
    ∃ y ∈ sphere c (2 * d),
      ((2 * Real.pi)⁻¹ * Real.log (3 / 2)) * (μ (A ∩ Λ)).toReal ≤
        (N : ℝ) * Λ.indicator (odometer μ R z t) y := by
  let : IsLocallyFiniteMeasure μ := hμ
  have hsub : ball c (2 * d) ⊆ ball 0 R :=
    ball_subset_closedBall.trans (hdisc.trans fun x hx => (hUsub hx).1)
  have hfinite : μ (ball c d ∩ Λ) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (measure_ball_lt_top (μ := μ))).ne
  have hc : c ∈ ball (0 : ℂ) R := hsub (mem_ball_self (by linarith))
  have hatom : μ {c} = 0 := hV.measure_singleton hc
  have hint : IntegrableOn (greenFunction (ball c (2 * d)) c) (ball c (2 * d) ∩ Λ) μ :=
    (integrable_greenFunction_of_volumeGrowth hR isOpen_ball hsub hV
      (ball_subset_closedBall hc)).mono_measure Measure.restrict_le_self
  obtain ⟨hqcont, hqΔ⟩ := restricted_greenPotential_center_regular hμ
    (by linarith : 0 < 2 * d) hV hsub (A := ball c (2 * d) ∩ Λ) inter_subset_left
  exact mass_le_truncated_odometer_of_disc_regular hμ hR hV hz ht hU hUsub hΛsub hcomp
    hd hdisc hmass hfinite hatom hint hqcont hqΔ

end HarmonicBalls.Section6

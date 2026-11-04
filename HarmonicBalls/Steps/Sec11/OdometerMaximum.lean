import HarmonicBalls.Steps.Sec11.SubharmonicMaximum
import HarmonicBalls.Proofs.Sec3.ConservationOfMass

/-!
# The finite-radius odometer and the maximum principle

The odometer is classically subharmonic away from its pole. This supplies
one of the deterministic hypotheses in the comparison chain of Lemma 11.6.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- The finite-radius odometer is continuous and classically subharmonic
on the disk with its pole removed. -/
theorem odometer_continuousOn_and_subharmonic {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βminus βplus) {p : ℂ} (hp : p ∈ ball (0 : ℂ) R)
    {t : ℝ} (ht : 0 < t) :
    ContinuousOn (odometer μ R p t) (ball 0 R \ {p}) ∧
      IsSubharmonicOn (ball 0 R \ {p}) (odometer μ R p t) := by
  let U := ball (0 : ℂ) R \ {p}
  have hUopen : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hUclosed : U ⊆ closedBall (0 : ℂ) R \ {p} :=
    fun x hx => ⟨ball_subset_closedBall hx.1, hx.2⟩
  obtain ⟨_, hvc, _, _, _⟩ :=
    obstacleLeastSuperharmonicMajorantGeneral_holds μ hμ R βminus βplus hR hV p hp t ht
  have hqc := greenPotentialBallContinuousStep_holds μ hμ R βminus βplus hR hV
  have hβc := continuousOn_obstacle (t := t) greenFunctionBall hR hp hqc
  have hsc : ContinuousOn (shiftedOdometer μ R p t) U := by
    exact (hvc.mono (hUclosed.trans sdiff_subset)).sub (hβc.mono hUclosed)
  have heq := (obstacleCompatibilityShiftStep_holds μ hμ R βminus βplus hR hV p hp t ht).2.2.2
  have heqU := heq.mono (hUclosed.trans sdiff_subset)
  have hoc : ContinuousOn (odometer μ R p t) U := hsc.congr heqU
  have hge := obstacleConservationOfMassStep1_holds μ hμ R βminus βplus hR hV p hp t ht
  have hle : LaplacianLE (-(shiftedOdometer μ R p t)) 0 U := by
    refine ⟨hge.1.neg, fun φ hφ hφ0 _ => ?_⟩
    have h := (hge.2 φ hφ hφ0).2
    simp only [integral_zero_measure, Pi.neg_apply, neg_mul, integral_neg] at h ⊢
    linarith
  have hsh : IsSubharmonicOn U (shiftedOdometer μ R p t) :=
    superharmonicOfLaplacianLEStep_holds U _ hUopen hsc.neg hle
  exact ⟨hoc, hsh.congr (fun x hx => congrArg Neg.neg (heqU hx).symm)⟩

/-- The maximum estimate in the Lemma 11.6 comparison chain for a
finite-radius odometer, provided the relevant closed disk avoids the pole. -/
theorem odometer_iSup_annulus_le_iSup_sphere {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βminus βplus) {p : ℂ} (hp : p ∈ ball (0 : ℂ) R)
    {t : ℝ} (ht : 0 < t) {z : ℂ} {a b : ℝ} (hb : 0 < b)
    (hcontain : closedBall z b ⊆ ball 0 R \ {p}) :
    (⨆ w ∈ annulus z a b, ENNReal.ofReal (odometer μ R p t w)) ≤
      ⨆ w ∈ sphere z b, ENNReal.ofReal (odometer μ R p t w) := by
  obtain ⟨hc, hs⟩ := odometer_continuousOn_and_subharmonic hμ hR hV hp ht
  have hball : ball z b ⊆ ball (0 : ℂ) R \ {p} := ball_subset_closedBall.trans hcontain
  have hs' : IsSubharmonicOn (ball z b) (odometer μ R p t) := by
    obtain ⟨hvc, hmean⟩ := hs
    exact ⟨hvc.mono hball, fun x hx r hr hsub => hmean x (hball hx) r hr (hsub.trans hball)⟩
  exact hs'.iSup_annulus_le_iSup_sphere hb (hc.mono hcontain)

/-- The finite-radius form of the deterministic comparison chain. The
mass-to-odometer and odometer-to-potential comparisons are explicit inputs. -/
theorem annulus_mass_le_of_odometer_comparison_bounds {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βminus βplus) {p : ℂ} (hp : p ∈ ball (0 : ℂ) R)
    {t : ℝ} (ht : 0 < t) (Λ : Set ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hcontain : ball z (5 * r) ⊆ ball 0 R \ {p}) (C₁ C₂ : ENNReal)
    (hmass : μ (annulus z r (2 * r) ∩ Λ) ≤
      C₁ * (⨆ w ∈ annulus z ((1 / 2) * r) (4 * r),
        ENNReal.ofReal (odometer μ R p t w)))
    (houter : (⨆ w ∈ annulus z (4 * r) (5 * r),
        ENNReal.ofReal (odometer μ R p t w)) ≤
      C₂ * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    μ (annulus z r (2 * r) ∩ Λ) ≤
      (C₁ * C₂) * annulusGreenPotentialSup μ z (3 * r) (6 * r) := by
  obtain ⟨hc, hs⟩ := odometer_continuousOn_and_subharmonic hμ hR hV hp ht
  have hball : ball z (4 * r) ⊆ ball (0 : ℂ) R \ {p} :=
    (ball_subset_ball (by linarith)).trans hcontain
  have hs' : IsSubharmonicOn (ball z (4 * r)) (odometer μ R p t) := by
    obtain ⟨hvc, hmean⟩ := hs
    exact ⟨hvc.mono hball, fun x hx ρ hρ hsub => hmean x (hball hx) ρ hρ (hsub.trans hball)⟩
  exact annulus_mass_le_of_subharmonic_comparison_bounds μ Λ _ z hr C₁ C₂
    hs' (hc.mono hcontain) hmass houter

end HarmonicBalls

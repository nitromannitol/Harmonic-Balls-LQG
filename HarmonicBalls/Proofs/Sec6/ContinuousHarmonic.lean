import HarmonicBalls.Proofs.Sec6.AnnulusHarmonicCorrection

/-! # Continuous distributional harmonic functions

The Poisson inequality for a superharmonic function and its negative gives
local equality with a Poisson integral, hence classical harmonicity.
-/

namespace HarmonicBalls.Section6

open Metric Set InnerProductSpace Filter
open scoped Topology

/-- A continuous function whose positive and negative are superharmonic on an
open set is classically harmonic there. -/
theorem harmonicOnNhd_of_superharmonic_and_neg {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hc : ContinuousOn f U)
    (hpos : IsSuperharmonicOn U f) (hneg : IsSuperharmonicOn U (-f)) :
    HarmonicOnNhd f U := by
  intro z hz
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let r := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsub : closedBall z r ⊆ U :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hδU
  have hi : CircleIntegrable f z r :=
    (hc.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le
  have hlo := discPoissonIntegral_le hpos.1 (hpos.localSuperMean hU) hr hsub hi
  have hhi := discPoissonIntegral_le hneg.1 (hneg.localSuperMean hU) hr hsub hi.neg
  have hnegP : ∀ w, discPoissonIntegral (-f) z r w = -discPoissonIntegral f z r w := by
    intro w
    simp only [discPoissonIntegral, Real.circleAverage, Pi.neg_apply,
      smul_neg, intervalIntegral.integral_neg]
  have heq : f =ᶠ[𝓝 z] discPoissonIntegral f z r := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    have h₁ := hlo w hw
    have h₂ := hhi w hw
    rw [hnegP] at h₂
    change -discPoissonIntegral f z r w ≤ -f w at h₂
    linarith
  exact (harmonicAt_congr_nhds heq).2
    (harmonicOnNhd_discPoissonIntegral hi z (mem_ball_self hr))

/-- The correction in Lemma 6.10 makes the odometer classically harmonic
and nonnegative on the annulus. -/
theorem exists_annulus_odometer_classical_harmonic_correction
    {μ : MeasureTheory.Measure ℂ} (hμ : MeasureTheory.IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) R \ {z}) :
    ∃ q : ℂ → ℝ,
      ContinuousOn q (annulus c a b) ∧ (∀ x, 0 ≤ q x) ∧
      (∀ x ∈ annulus c a b, ENNReal.ofReal (q x) ≤ annulusGreenPotentialSup μ c a b) ∧
      (∀ x ∈ annulus c a b, 0 ≤ odometer μ R z t x + q x) ∧
      HarmonicOnNhd (fun x => odometer μ R z t x + q x) (annulus c a b) := by
  obtain ⟨q, hqc, hq0, hbound, hsum0, _, hsup, hinf⟩ :=
    exists_annulus_odometer_harmonic_correction hμ hR hV hz ht hab hb hA
  have hcont : ContinuousOn (fun x => odometer μ R z t x + q x) (annulus c a b) :=
    ((odometer_continuousOn_and_subharmonic hμ hR hV hz ht).1.mono hA).add hqc
  exact ⟨q, hqc, hq0, hbound, hsum0,
    harmonicOnNhd_of_superharmonic_and_neg (isOpen_ball.sdiff isClosed_closedBall) hcont hsup hinf⟩

end HarmonicBalls.Section6

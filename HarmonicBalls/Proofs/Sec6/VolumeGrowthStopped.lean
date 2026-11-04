import HarmonicBalls.Proofs.Sec6.GreenUniformBound
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-! # Stopped Green potentials under volume growth

The deterministic disc Hölder estimate supplies the regularity in the stopped
potential argument for locally finite measures satisfying volume growth.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric InnerProductSpace ProbabilityTheory MarkovProcess
open scoped NNReal ENNReal ContDiff ZeroAtInfty

/-- The restricted Green potential in a disc is harmonic off its compact
support under the volume-growth condition. -/
theorem harmonicOnNhd_restricted_greenPotential_ball_of_volumeGrowth
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {L : Set ℂ} (hL : IsCompact L) (hLU : L ⊆ ball (0 : ℂ) R) :
    HarmonicOnNhd (fun z => ∫ x in L, greenFunction (ball 0 R) z x ∂μ) (ball 0 R \ L) := by
  apply harmonicOnNhd_restricted_greenPotential_ball_of_holder hL hLU hL.measure_lt_top
  intro f hf
  rw [closure_ball (0 : ℂ) hR.ne'] at hf ⊢
  exact greenPotential_ball_holderOnWith hR hV hf

/-- The stopped restricted-potential bound under volume growth, conditional on
the planar heat generator identification for smooth compactly supported functions. -/
theorem restricted_greenPotential_ball_stopped_representation_of_volumeGrowth
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {L : Set ℂ} (hL : IsCompact L) (hLU : L ⊆ ball (0 : ℂ) R)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) R \ L)
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ENNReal.ofReal (∫ y in L, greenFunction (ball 0 R) x y ∂μ) ≤ ∫⁻ path,
      ENNReal.ofReal (∫ y in L,
        greenFunction (ball 0 R) (path ((ContinuousPath.exitTime (ball 0 R \ L) path).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x) := by
  apply restricted_greenPotential_stopped_representation_of_harmonic isOpen_ball isBounded_ball
    hL hLU ?_ hx (harmonicOnNhd_restricted_greenPotential_ball_of_volumeGrowth hR hV hL hLU) hgen
  intro f hf
  rw [closure_ball (0 : ℂ) hR.ne'] at hf ⊢
  exact greenPotential_ball_holderOnWith hR hV hf

end HarmonicBalls.Section6

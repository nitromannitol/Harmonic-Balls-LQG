import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen

/-! # Harmonic minorants on open domains

The greatest harmonic minorant of the Newtonian kernel is harmonic on an open
set containing its pole whenever a real harmonic minorant exists.
-/

namespace HarmonicBalls

open Metric Set InnerProductSpace Filter

/-- A harmonic minorant of the Newtonian kernel implies harmonicity of its
pointwise greatest harmonic minorant, without a boundedness assumption. -/
theorem harmonicOnNhd_greatestHarmonicMinorant_newtonKernel_of_exists
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hex : ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h) :
    HarmonicOnNhd (fun y => (greatestHarmonicMinorant U (newtonKernelEReal z) y).toReal) U := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hball : closedBall z (2 * ε) ⊆ U :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hδU
  obtain ⟨h, hh⟩ := hex
  have hreg := (isHarmonicMinorant_regularized_iff hε hball).1 hh
  have hlow : ∀ y ∈ U, h y ≤ regularizedNewtonKernel ε z y := by
    intro y hy
    exact EReal.coe_le_coe_iff.mp (hreg.2 y hy)
  have hcont : ContinuousOn (regularizedNewtonKernel ε z) U :=
    (continuous_regularizedNewtonKernel_right hε z).continuousOn
  have hmean := hasLocalSuperMean_regularizedNewtonKernel hε z U
  have hsweep := (sweep_limit hU hcont hmean hreg.1 hlow).1
  intro y hy
  apply (harmonicAt_congr_nhds ?_).2 (hsweep y hy)
  filter_upwards [hU.mem_nhds hy] with w hw
  rw [greatestHarmonicMinorant_regularized hε hball,
    greatestHarmonicMinorant_eq_of_sweep_limit hU hcont hmean hreg.1 hlow w hw,
    EReal.toReal_coe]

end HarmonicBalls
